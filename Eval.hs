{-# LANGUAGE TupleSections #-}

module Eval where

import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Error
import Data.Maybe
import Data.Char
import System.IO.Unsafe
import System.IO.Error hiding (try)
import Control.Exception hiding (try, block)
import Data.IORef
import Data.StateVar
import qualified Data.Map as M
import Data.Map (Map, (!))
import qualified Data.Set as S
import Data.Set (Set)
import System.Exit
import System.Directory
import qualified System.IO.Strict as Strict
import System.IO
import Data.Foldable (asum, toList)
import Debug.Trace
import System.Process
import Control.Concurrent.BoundedChan

import Util

import Expr


isNilop (EObj (FnObj params _ _)) = all isNilop' params
isNilop _ = False

isNilop' (OptParam {}) = True
isNilop' (RepParam {}) = True
isNilop' _ = False

evalID derefVars (EId (id,accessType)) notFoundMsg env = do
  val <- envLookup id env
  case val of
    Nothing -> throwError $ notFoundMsg ++ id
    Just (val, accessType2) -> do
      val <- case (accessType,accessType2) of
        (ByVal, ByVal) -> pure val
        (ByVal, ByName) -> eval' val env
        (ByName, ByName) -> pure val
        (ByName, ByVal) -> throwError $ "Invalid use of ~: " ++ prettyPrint val
      if derefVars then (case val of
        EVar var -> (,env) <$> lift (get var)
        val -> pure (val,env))
      else pure (val,env)

evalID' derefVars id notFoundMsg env = fst <$> evalID derefVars id notFoundMsg env

lookupID id = evalID' True (EId (id,ByVal)) "Identifier not found: "

--Similar to rawSystem, but also handles commands like "sbt" and "clear"
--myRawSystem command args = system (intercalate " " $ map parenify (command:args))
--  where parenify str = if any isSpace str then "\"" ++ str ++ "\"" else str
myRawSystem = rawSystem

maybeEvalID derefVars (EId (id,accessType)) env = do
  val <- envLookup id env
  case val of
    Nothing -> pure Nothing
    Just (val, accessType2) -> do
      val <- case (accessType,accessType2) of
        (ByVal, ByVal) -> pure val
        (ByVal, ByName) -> eval' val env
        (ByName, ByName) -> pure val
        (ByName, ByVal) -> throwError $ "Invalid use of ~: " ++ prettyPrint val
      if derefVars then (case val of
        EVar var -> Just <$> lift (get var)
        val -> pure $ Just val)
      else pure $ Just val

eval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
eval EVoid env = pure (EVoid, env)
eval id@(EId {}) env = do
  id' <- maybeEvalID True id env
  case id' of
    Just id -> pure (id, env)
    Nothing -> case id of
      EId (id, ByVal) -> pure (EExec id [], env)
      EId (id, ByName) -> throwError "Can't call a foreign program by-name!"
eval (EGetVar var) env = evalID False (EId var) "Variable not found: " env
eval (EMemberAccess obj id) env = do
  obj <- eval' obj env
  case obj of
    EObj (Obj oenv) -> do
      val <- evalID' True (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    EObj (PrimObj prim oenv) -> do
      val <- evalID' True (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    EExec prog args -> pure (EExec prog (args++[id]), env)
    x -> throwError $ "Can't access member " ++ id ++ " on non-object: " ++ prettyPrint x
eval (EMemberAccessGetVar obj id) env = do
  obj <- eval' obj env
  case obj of
    EObj (Obj oenv) -> do
      val <- evalID' False (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    EObj (PrimObj prim oenv) -> do
      val <- evalID' False (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    EExec prog args -> pure (EExec prog (args++[id]), env)
    x -> throwError $ "Can't access member " ++ id ++ " on non-object: " ++ prettyPrint x
eval (EObj (FnObj params (Fn body) fnEnv)) env = do
  verifyParams params
  pure (EObj (FnObj params (Closure body env) fnEnv), env)
eval prim@(EObj (FnObj _ (Prim _) _)) env = pure (prim, env) --This is necessary for evaulating lists and tuples; it should never happen in any other case; TODO: can this be removed?
eval closure@(EObj (FnObj _ (Closure _ _) _)) env = pure (closure,env) --TODO: this used to give an error but is now enabled; why?
eval (EObj obj) env = pure (EObj obj, env)
eval (EBlock []) env = pure (EVoid, env)
eval (EBlock exprs) env = do
  env' <- envNewScope env
  vals <- forM exprs $ \expr -> eval expr env'
  pure (fst $ last vals, env)
eval (EFnApp fn args) env = do
  (fn,_) <- eval fn env
  case fn of
    EExec prog firstArgs -> do
      verifyArgs args
      args' <- getExecArgs args env
      res <- lift $ tryJust (guard . isDoesNotExistError) (myRawSystem prog (firstArgs ++ args'))
      case res of
        Left err -> throwError $ "Identifier or program not found: " ++ prog
        Right res -> pure (EVoid, env)
    EObj (FnObj params fnBody fnEnv) -> do
      let
        evalFnApp = case fnBody of
          Closure body closure -> do
            verifyArgs args
            args' <- matchParams params args env
            bodyEnv <- envNewScope closure
            forM_ args' $ \(name,accessType,val) -> envDefine name bodyEnv (pure ((val,accessType),val))
            (res,_) <- eval body bodyEnv
            pure (res,env)
          Prim fn -> do
            verifyArgs args
            args' <- matchParams params args env
            bodyEnv <- envNewScope env
            forM_ args' $ \(name,accessType,val) -> envDefine name bodyEnv (pure ((val,accessType),val))
            (res,_) <- fn bodyEnv
            pure (res,env)
          Fn f -> throwError $ "Evaluating a function call of a non-closure: " ++ show (params,f,args)
      case args of
        (Arg (EId (id,ByVal)):args) -> do
          val <- envLookup id =<< lift (envStackFromEnv fnEnv)
          case val of
            Just (val,ByVal) -> eval (EFnApp val args) env
            Nothing -> evalFnApp
        _ -> evalFnApp
    EObj obj -> case args of
      [] -> pure (EObj obj,env) --This is the case when you have a lone identifier
      args -> throwError ("Invalid function: " ++ prettyPrint (EObj obj))
    EVoid -> case args of
      [] -> pure (EVoid,env)
      args -> throwError ("Invalid function: " ++ prettyPrint EVoid)
    x -> throwError ("Invalid function: " ++ prettyPrint x)
eval (ENew exprs) env = do
  env' <- envNewScope env
  forM_ exprs $ \expr -> eval expr env'
  obj <- envHead env'
  pure (EObj (Obj obj), env)
eval (EWith a b) env = do
  (a', _) <- eval a env
  (b', _) <- eval b env
  case (a',b') of
    (EObj (Obj a), EObj (Obj b)) -> pure (EObj . Obj $ M.union b a, env) --In the union, b must come before a because M.union is left-biased
    _ -> throwError "Invalid arguments to 'with'; both of them must be objects."
eval (EIf cond t f) env = do
  (cond',_) <- eval cond env
  case cond' of
    EObj (PrimObj (PBool True) _) -> ((,env) . fst) <$> eval t env
    EObj (PrimObj (PBool False) _) -> ((,env) . fst) <$> eval f env
    c -> throwError $ "Invalid condition for if: " ++ prettyPrint c
eval (EDef id val) env = envDefine id env $ do
  (val,_) <- eval val env
  val' <- lift $ (,ByVal) . EVar <$> newIORef val
  pure (val', val)
eval (EAssign var val) env = do
  (var,_) <- eval var env
  (val',_) <- eval val env
  case var of
    EVar var -> lift $ var $= val'
    x -> throwError $ "Not a variable: " ++ prettyPrint x
  pure (val', env)
eval (EValClosure expr closure) env = (,env) <$> eval' expr closure
eval x _ = throwError $ "eval unimplemented for " ++ show x


--Like regular eval, but allows you to redefine things
replEval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
replEval (EDef id val) env = envRedefine id env $ do
  (val,_) <- replEval val env
  val' <- lift $ (,ByVal) . EVar <$> newIORef val
  pure (val', val)
replEval expr env = eval expr env

apply f args = eval' (EFnApp f args)
call obj f args = eval' (EFnApp (EMemberAccess (EObj obj) f) args)
evalApply obj args = eval (EFnApp (EMemberAccess (EObj obj) "apply") args)

eval' expr env = fst <$> eval expr env
replEval' expr env = fst <$> replEval expr env

getStr expr env = case getString' expr of
  Just str -> pure [str]
  Nothing -> case expr of
    EObj (PrimObj (PList xs) _) -> concatMapM (`getStr` env) xs
    EObj obj -> do
      res <- call obj "toString" [] env
      case getString' res of
        Just str -> pure [str]
        Nothing -> throwError $ "Invalid result from toString: " ++ prettyPrint res
    x -> throwError $ "Invalid argument to program: " ++ prettyPrint x

evalToStr expr env = (`getStr` env) =<< eval' expr env

getExecArgs :: [Arg] -> EnvStack -> IOThrowsError [String]
getExecArgs [] env = pure []
getExecArgs (Arg arg:args) env = (++) <$> evalToStr arg env <*> getExecArgs args env
getExecArgs (KeywordArg str arg:args) env = (("--"++str) :) <$> ((++) <$> evalToStr arg env <*> getExecArgs args env)
getExecArgs (ListArg xs:args) env = do
  listArgs <- getList =<< eval' xs env
  getExecArgs (ListArgNoEval listArgs:args) env
getExecArgs (ListArgNoEval xs:args) env = (++) <$> concatMapM (`getStr` env) xs <*> getExecArgs args env
getExecArgs (FlagArg flag:args) env = (("-"++flag):) <$> getExecArgs args env
getExecArgs (LongFlagArg flag:args) env = (("--"++flag):) <$> getExecArgs args env

matchArg :: Bool -> String -> AccessType -> Expr -> EnvStack -> IOThrowsError (String,AccessType,Expr)
matchArg evaluate name accessType arg env = do
  (arg',_) <- case accessType of
    ByVal -> if evaluate then eval arg env else pure (EValClosure arg env,env)
    ByName -> case arg of
      (EId (_,ByName)) -> if evaluate then eval arg env else pure (EValClosure arg env,env) --We must evaluate in this case or we end up trying to treat an identifier as a value when calling a function with something prefixed with ~, which occurs in functions like "while"
      _ -> pure (EValClosure arg env, env)
  pure (name,accessType,arg')

matchParams' :: [Param] -> Expr -> [Arg] -> Bool -> EnvStack -> IOThrowsError [(String,AccessType,Expr)]
matchParams' (ReqParam (name,accessType)  :params) arg args evaluate env = (:) <$> matchArg evaluate name accessType arg env <*> matchParams params args env
matchParams' (OptParam (name,accessType) _:params) arg args evaluate env = (:) <$> matchArg evaluate name accessType arg env <*> matchParams params args env


matchParams :: [Param] -> [Arg] -> EnvStack -> IOThrowsError [(String,AccessType,Expr)]
matchParams [] [] _ = pure []
matchParams params@(ReqParam {}:_) (Arg arg:args) env = matchParams' params arg args True env
matchParams params@(OptParam {}:_) (Arg arg:args) env = matchParams' params arg args True env
matchParams params (ListArgNoEval []:args) env = matchParams params args env
matchParams params@(ReqParam {}:_) (ListArgNoEval (arg:lArgs):args) env = do
  matchParams' params arg (ListArgNoEval lArgs:args) False env
matchParams params@(OptParam {}:_) (ListArgNoEval (arg:lArgs):args) env = do
  matchParams' params arg (ListArgNoEval lArgs:args) False env
matchParams params (ListArg xs:args) env = do
  listArgs <- getList =<< eval' xs env
  matchParams params (ListArgNoEval listArgs:args) env
matchParams (OptParam (name,accessType) def:params) [] env = (:) <$> matchArg True name accessType def env <*> matchParams params [] env
matchParams [RepParam (name,accessType)] args env = do
  args <- concat <$> (forM args $ \arg -> case arg of
    Arg arg -> (:[]) <$> eval' arg env
    ListArg xs -> getList =<< eval' xs env
    ListArgNoEval args -> pure args
    KeywordArg k arg -> throwError $ "Can't pass keyword argument to repeated parameter: " ++ prettyPrint k ++ ":" ++ prettyPrint arg)
  pure [(name, accessType, makeList args)]
matchParams params_ (KeywordArg k arg:args) env = do
  params <- takeKeywordArg params_ k
  matchParams' params arg args True env
matchParams params_ (FlagArg flag:args) env = do
  params <- takeFlagParam params_ flag
  (:) (flag,ByVal,makeBool True) <$> matchParams params args env
matchParams (FlagParam flag:params) args_ env = do
  (args,match) <- takeFlagArg args_ flag
  (:) (flag,ByVal,makeBool match) <$> matchParams params args env
matchParams params_ (LongFlagArg flag:args) env = throwError $ "Long flag syntax is only supported when calling external scripts: --" ++ flag
matchParams params [] env = throwError $ "Not enough arguments for function; unspecified arguments: " ++ intercalate ", " (map prettyPrint params)
matchParams [] args env = throwError $ "Too many arguments for function; extra arguments: " ++ intercalate ", " (map prettyPrint args)
matchParams params args env = throwError $ "matchParams unimplemented for " ++ show (params,args)

takeKeywordArg :: [Param] -> String -> IOThrowsError [Param]
takeKeywordArg params name = case length match of
  0 -> throwError $ "No match for keyword argument " ++ name
  1 -> pure (head match : noMatch)
  _ -> throwError $ "Multiple matches for keyword argument " ++ name ++ ". This indicates a bug in the interpreter; this problem should have been caught when the invalid function was declared."
  where
    (match, noMatch) = flip partition params $ \param -> case param of
      ReqParam (name',_)   -> name == name'
      OptParam (name',_) _ -> name == name'

takeFlagParam :: [Param] -> String -> IOThrowsError [Param]
takeFlagParam params flag = do
  (match, noMatch) <- flip partitionM params $ \param -> case param of
    FlagParam flag' -> pure $ flag == flag'
    _ -> throwError "Invalid flag."
  case length match of
    0 -> throwError $ "No match for flag " ++ flag
    1 -> pure noMatch
    _ -> throwError $ "Multiple matches for flag " ++ flag ++ ". This indicates a bug in the interpreter; this problem should have been caught when the invalid function was declared."

takeFlagArg :: [Arg] -> String -> IOThrowsError ([Arg],Bool)
takeFlagArg args flag = do
  (match, noMatch) <- flip partitionM args $ \arg -> case arg of
    FlagArg flag' -> pure $ flag == flag'
    _ -> throwError "Invalid flag."
  case length match of
    0 -> pure (args, False)
    1 -> pure (noMatch, True)
    _ -> throwError $ "Multiple matches for flag " ++ flag ++ ". This indicates a bug in the interpreter; this problem should have been caught when the invalid function was declared."

verifyParams :: [Param] -> IOThrowsError ()
verifyParams = verifyParams' S.empty where
  verifyParams' :: Set String -> [Param] -> IOThrowsError ()
  verifyParams' set [] = pure ()
  verifyParams' set (ReqParam name:  params) = verifyID set name params
  verifyParams' set (OptParam name _:params) = verifyID set name params
  verifyParams' set (RepParam name:  params) = verifyID set name params
  verifyParams' set (FlagParam name: params) = verifyID set (name,ByVal) params
  verifyID set (name,_) params = if S.member name set then throwError $ "Two definitions for parameter " ++ name
    else verifyParams' (S.insert name set) params

verifyArgs :: [Arg] -> IOThrowsError ()
verifyArgs = verifyArgs' S.empty where
  verifyArgs' :: Set String -> [Arg] -> IOThrowsError ()
  verifyArgs' set [] = pure ()
  verifyArgs' set (Arg EUnknown:args) = error "UnknownArg in verifyArgs'"
  verifyArgs' set (Arg _:args) = verifyArgs' set args
  verifyArgs' set (ListArg _:args) = verifyArgs' set args
  verifyArgs' set (KeywordArg key _:args) = if S.member key set then throwError $ "Two definitions for keyword argument " ++ key
    else verifyArgs' (S.insert key set) args
  verifyArgs' set (FlagArg flag:args) = if S.member flag set then throwError $ "Two definitions for flag argument " ++ flag
    else verifyArgs' (S.insert flag set) args
  verifyArgs' set (LongFlagArg flag:args) = if S.member flag set then throwError $ "Two definitions for flag argument " ++ flag
    else verifyArgs' (S.insert flag set) args
  verifyArgs' set (RestArgs:args) = error "RestArgs in verifyArgs'"


envLookup' name env = eval' (EId (name,ByVal)) env


makeInt a = EObj $ PrimObj (PInt a) $ envFromList [
  ("to", primUnop $ \x -> case x of
    PInt b -> pure $ makeList $ map makeInt [a..b]
    _ -> throwError "Invalid argument to 'to'"),
  ("until", primUnop $ \x -> case x of
    PInt b -> pure $ makeList $ map makeInt [a..b-1]
    _ -> throwError "Invalid argument to 'to'"),
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("+", primUnop $ onNum (a+) (fromInteger a+)),
  ("-", primUnop $ onNum (a-) (fromInteger a-)),
  ("*", primUnop $ onNum (a*) (fromInteger a*)),
  ("/", primUnop $ onFloat (fromInteger a/)),
  ("%", primUnop $ onNum (mod a) (fmod (fromInteger a))),
  ("^", primUnop $ onNum (a^) (fromInteger a**)),
  ("div", primUnop $ onInt (a `div`)),
  ("gcd", primUnop $ onInt (a `gcd`)),
  ("lcm", primUnop $ onInt (a `lcm`)),
  (">", primUnop $ onNumToBool (a>) (fromInteger a>)),
  ("<", primUnop $ onNumToBool (a<) (fromInteger a<)),
  (">=", primUnop $ onNumToBool (a>=) (fromInteger a>=)),
  ("<=", primUnop $ onNumToBool (a<=) (fromInteger a<=)),
  ("==", primUnop $ onNumToBool (a==) (fromInteger a==)),
  ("!=", primUnop $ onNumToBool (a/=) (fromInteger a/=)),
  ("abs", nilop $ pure (makeInt $ abs a)),
  ("sign", nilop $ pure (makeInt $ signum a)),
  ("logBase", primUnop $ onFloat (logBase $ fromInteger a)),
  ("atan2", primUnop $ onFloat (atan2 $ fromInteger a)),
  ("ln", floatNilop . log $ fromInteger a),
  ("log", floatNilop . (logBase 10) $ fromInteger a),
  ("lg", floatNilop . (logBase 2) $ fromInteger a),
  ("exp", floatNilop . exp $ fromInteger a),
  ("sqrt", floatNilop . sqrt $ fromInteger a),
  ("sin", floatNilop . sin $ fromInteger a),
  ("cos", floatNilop . cos $ fromInteger a),
  ("tan", floatNilop . tan $ fromInteger a),
  ("asin", floatNilop . asin $ fromInteger a),
  ("acos", floatNilop . acos $ fromInteger a),
  ("atan", floatNilop . atan $ fromInteger a),
  ("sinh", floatNilop . sinh $ fromInteger a),
  ("cosh", floatNilop . cosh $ fromInteger a),
  ("tanh", floatNilop . tanh $ fromInteger a),
  ("asinh", floatNilop . asinh $ fromInteger a),
  ("acosh", floatNilop . acosh $ fromInteger a),
  ("atanh", floatNilop . atanh $ fromInteger a)
  ]
makeFloat :: Double -> Expr
makeFloat a = EObj $ PrimObj (PFloat a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("+", primUnop $ onFloat (a+)),
  ("-", primUnop $ onFloat (a-)),
  ("*", primUnop $ onFloat (a*)),
  ("/", primUnop $ onFloat (a/)),
  ("%", primUnop $ onFloat (fmod a)),
  ("^", primUnop $ onFloat (a**)),
  (">", primUnop $ onFloatToBool (a>)),
  ("<", primUnop $ onFloatToBool (a<)),
  (">=", primUnop $ onFloatToBool (a>=)),
  ("<=", primUnop $ onFloatToBool (a<=)),
  ("==", primUnop $ onFloatToBool (a==)),
  ("!=", primUnop $ onFloatToBool (a/=)),
  ("abs", floatNilop $ abs a),
  ("sign", floatNilop $ signum a),
  ("floor", nilop . pure . makeInt $ floor a),
  ("ceil", nilop . pure . makeInt $ ceiling a),
  ("truncate", nilop . pure . makeInt $ truncate a),
  ("round", nilop . pure . makeInt $ round a),
  ("isNaN", nilop . pure . makeBool $ isNaN a),
  ("isInfinite", nilop . pure . makeBool $ isInfinite a),
  ("isDenormalized", nilop . pure . makeBool $ isDenormalized a),
  ("isNegativeZero", nilop . pure . makeBool $ isNegativeZero a),
  ("logBase", primUnop $ onFloat (logBase a)),
  ("atan2", primUnop $ onFloat (atan2 a)),
  ("ln", floatNilop $ log a),
  ("log", floatNilop $ (logBase 10) a),
  ("lg", floatNilop $ (logBase 2) a),
  ("exp", floatNilop $ exp a),
  ("sqrt", floatNilop $ sqrt a),
  ("sin", floatNilop $ sin a),
  ("cos", floatNilop $ cos a),
  ("tan", floatNilop $ tan a),
  ("asin", floatNilop $ asin a),
  ("acos", floatNilop $ acos a),
  ("atan", floatNilop $ atan a),
  ("sinh", floatNilop $ sinh a),
  ("cosh", floatNilop $ cosh a),
  ("tanh", floatNilop $ tanh a),
  ("asinh", floatNilop $ asinh a),
  ("acosh", floatNilop $ acosh a),
  ("atanh", floatNilop $ atanh a)
  ]
makeChar a = EObj $ PrimObj (PChar a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a))
  ]
makeBool a = EObj $ PrimObj (PBool a) $ envFromList [
  ("toString", nilop $ case a of
    True -> pure (makeString "true")
    False -> pure (makeString "false")),
  ("&&", primUnop $ onBool (a&&)),
  ("||", primUnop $ onBool (a||))
  ]
makeString = makeList . map makeChar

makeList a = EObj $ PrimObj (PList a) $ envFromList [
  ("toString", nilop $ case getString3' a of
    Just str -> pure (makeString str)
    Nothing -> pure (makeString $ prettyPrint a)),
  ("head", nilop $ if null a then throwError "Can't take the head of an empty list" else pure (head a)),
  ("tail", nilop $ if null a then throwError "Can't take the tail of an empty list" else pure (makeList $ tail a)),
  ("init", nilop $ if null a then throwError "Can't take the init of an empty list" else pure (makeList $ init a)),
  ("last", nilop $ if null a then throwError "Can't take the last of an empty list" else pure (last a)),
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("::", unop $ \b -> pure $ makeList (b:a)),
  ("++", primUnop $ \x -> case x of
    PList b -> pure $ makeList (a++b)
    _ -> throwError "Invalid argument to ++"),
  ("apply", primUnop $ onInt' (index a)),
  ("map", unop' $ \fn env -> (,env) <$> makeList <$> mapM (flip (apply fn) env . (:[]) . Arg) a),
  ("filter", unop' $ \fn env -> (,env) <$> makeList <$> filterM (getBool <=< flip (apply fn) env . (:[]) . Arg) a)
  ]
makeTuple a = EObj $ PrimObj (PTuple a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("apply", primUnop $ onInt' (index a))
  ]
makeGen cap = do
  ioRef <- lift $ newIORef Nothing
  chan <- lift $ newBoundedChan cap
  done <- lift $ newIORef False
  pure $ EObj $ PrimObj (PGen ioRef chan) $ envFromList [
    ("cur", nilop $ do
      val <- lift $ readIORef ioRef
      case val of
        Just val -> pure val
        Nothing -> throwError "Generator has no current value"),
    ("moveNext", nilop $ do
      done' <- lift $ readIORef done
      if done' then pure (makeBool False) else do
      val <- lift $ readChan chan
      lift $ writeIORef ioRef val
      let gotOne = isJust val
      lift $ writeIORef done (not gotOne)
      pure (makeBool gotOne))
    ]
makeHandle handle file = EObj $ PrimObj (PHandle handle file) $ envFromList [
  ("atEOF", nilop $ makeBool <$> lift (hIsEOF handle)),
  ("readChar", nilop $ do
    eof <- lift $ hIsEOF handle
    if eof then pure EVoid else makeChar <$> lift (hGetChar handle)),
  ("writeChar", objUnop $ \obj -> case obj of
    PrimObj (PChar char) _ -> do
      lift $ hPutChar handle char
      pure EVoid
    _ -> throwError $ "Invalid argument to writeChar: " ++ prettyPrint obj)
  ]


--These functions are necessary so that "(x,y)" evaluates its arguments before creating the tuple/list/whatever
makeList' xs = EFnApp makeListPrim (map Arg xs)
makeTuple' xs = EFnApp makeTuplePrim (map Arg xs)

makeListPrim = ePrim [repParam "xs"] (\env -> (,env) . makeList . fromEList <$> envLookup' "xs" env)
makeTuplePrim = ePrim [repParam "xs"] (\env -> (,env) . makeTuple . fromEList <$> envLookup' "xs" env)

index :: [a] -> Integer -> IOThrowsError a
index xs i = if i >= 0 && i < genericLength xs then pure (xs `genericIndex` i) else throwError "Invalid index!"



--TODO: turn this into a type class?
desugar :: Expr -> Expr
desugar EVoid = EVoid
desugar (EId id) = EId id
desugar (EFnApp EUnknown []) = EUnknown
desugar (EFnApp fn args) = processUnknownArgs (desugar fn) (map desugarArg args)
desugar (EMemberAccess a b) = EMemberAccess (desugar a) b
desugar (EDef name val) = EDef name (desugar val)
desugar (EAssign a b) = EAssign (desugar a) (desugar b)
desugar (EVar _) = error "Can't have an EVar in desugar!"
desugar (EGetVar id) = EGetVar id
desugar (EMemberAccessGetVar a b) = EMemberAccessGetVar (desugar a) b
desugar (EBlock xs) = EBlock (map desugar xs)
desugar (ENew xs) = ENew (map desugar xs)
desugar (EWith a b) = EWith (desugar a) (desugar b)
desugar (EObj x) = EObj $ desugarObj x
desugar (EIf a b c) = EIf (desugar a) (desugar b) (desugar c)
desugar EUnknown = EUnknown

desugarObj :: Obj -> Obj
desugarObj (Obj env) = Obj env
desugarObj (PrimObj primData env) = PrimObj primData env
desugarObj (FnObj params fn env) = FnObj (map desugarParam params) (desugarFn fn) env

desugarFn :: Fn -> Fn
desugarFn (Prim x) = Prim x
desugarFn (Fn body) = Fn (desugar body)
desugarFn (Closure {}) = error "Can't have a closure in desugarFn!"

fnEnv fn = envFromList [
  ("o", unop' $ \fn2 env -> do
    compose <- lookupID "compose" env
    (,env) <$> apply compose [Arg fn, Arg fn2] env)
  ]

--These are defined in an unusual way. The function effectively contains a copy of itself in the environment. This is necessary in order for the environment to be able to use the function in computations.
eFn params body = let fn = EObj (FnObj params (Fn body) (fnEnv fn)) in fn
ePrim params body = let fn = EObj (FnObj params (Prim body) (fnEnv fn)) in fn

processUnknownArgs :: Expr -> [Arg] -> Expr
--TODO: support the case where the fn is EMemberAccess and there's no params
processUnknownArgs (EMemberAccess obj field) [] = if isUnknown obj
  then eFn [reqParam "_a"] (EFnApp (EMemberAccess (eId "_a") field) [])
  else EFnApp (EMemberAccess obj field) []
processUnknownArgs fn [] = EFnApp fn []
--TODO: remove this code duplication
processUnknownArgs (EMemberAccess obj field) args = case (isUnknown obj, not (null unknowns), hasRestArgs) of
  (False,_,True) -> eFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp (EMemberAccess obj field) (replaceUnknowns args 0))
  (True,_,True) -> eFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp (EMemberAccess (eId "_a") field) (replaceUnknowns args 1))
  (True,_,False) -> eFn (map reqParam unknowns) (EFnApp (EMemberAccess (eId "_a") field) (replaceUnknowns args 1))
  (False,True,False) -> eFn (map reqParam unknowns) (EFnApp (EMemberAccess obj field) (replaceUnknowns args 0))
  (False,False,False) -> EFnApp (EMemberAccess obj field) args
  where
    name i = "_" ++ [chr (i + ord 'a')]
    objUnknowns = if isUnknown obj then 1 else 0
    unknowns = map name [0..objUnknowns+countBy isUnknownArg args-1]
    hasRestArgs = if null args then False else isRestArgs (last args)
    replaceUnknowns [] i = []
    replaceUnknowns (Arg EUnknown:args) i = Arg (eId $ name i) : replaceUnknowns args (i+1)
    replaceUnknowns [RestArgs] i = [ListArg (eId "_xs")]
    replaceUnknowns (arg:args) i = arg : replaceUnknowns args i
processUnknownArgs fn args = case (isUnknown fn, not (null unknowns), hasRestArgs) of
  (False,_,True) -> eFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp fn (replaceUnknowns args 0))
  (True,_,True) -> eFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp (eId "_a") (replaceUnknowns args 1))
  (True,_,False) -> eFn (map reqParam unknowns) (EFnApp (eId "_a") (replaceUnknowns args 1))
  (False,True,False) -> eFn (map reqParam unknowns) (EFnApp fn (replaceUnknowns args 0))
  (False,False,False) -> EFnApp fn args
  where
    name i = "_" ++ [chr (i + ord 'a')]
    fnUnknowns = if isUnknown fn then 1 else 0
    unknowns = map name [0..fnUnknowns+countBy isUnknownArg args-1]
    hasRestArgs = if null args then False else isRestArgs (last args)
    replaceUnknowns [] i = []
    replaceUnknowns (Arg EUnknown:args) i = Arg (eId $ name i) : replaceUnknowns args (i+1)
    replaceUnknowns [RestArgs] i = [ListArg (eId "_xs")]
    replaceUnknowns (arg:args) i = arg : replaceUnknowns args i

isUnknown EUnknown = True
isUnknown _ = False

isUnknownArg (Arg EUnknown) = True
isUnknownArg _ = False

isRestArgs RestArgs = True
isRestArgs _ = False

desugarParam (ReqParam id) = ReqParam id
desugarParam (OptParam id expr) = OptParam id (desugar expr)
desugarParam (RepParam id) = RepParam id
desugarParam (FlagParam flag) = FlagParam flag

desugarArg (Arg expr) = Arg (desugar expr)
desugarArg (KeywordArg id expr) = KeywordArg id (desugar expr)
desugarArg (ListArg expr) = ListArg (desugar expr)
desugarArg (ListArgNoEval {}) = error "Can't have ListArgNoEval in desugarArg!"
desugarArg RestArgs = RestArgs
desugarArg (FlagArg flag) = FlagArg flag
desugarArg (LongFlagArg flag) = LongFlagArg flag



prim :: [String] -> (Map String Expr -> IOThrowsError Expr) -> Expr
prim args f = ePrim (map reqParam args) $ \env -> (,env) <$> (f =<< M.fromList <$> mapM (\arg -> (arg,) <$> envLookup' arg env) args)

prim' :: [String] -> (Map String Expr -> EnvStack -> IOThrowsError (Expr,EnvStack)) -> Expr
prim' args f = ePrim (map reqParam args) $ \env -> (flip f env =<< M.fromList <$> mapM (\arg -> (arg,) <$> envLookup' arg env) args)

nilop :: IOThrowsError Expr -> Expr
nilop ret = prim [] (const ret)

nilop' :: (EnvStack -> IOThrowsError (Expr,EnvStack)) -> Expr
nilop' ret = prim' [] (\map env -> ret env)

floatNilop = nilop . pure . makeFloat

unop :: (Expr -> IOThrowsError Expr) -> Expr
unop f = prim ["x"] $ \args -> f (args!"x")

unop' :: (Expr -> EnvStack -> IOThrowsError (Expr,EnvStack)) -> Expr
unop' f = prim' ["x"] $ \args -> f (args!"x")

binop :: (Expr -> Expr -> IOThrowsError Expr) -> Expr
binop f = prim ["x", "y"] $ \args -> f (args!"x") (args!"y")

triop :: (Expr -> Expr -> Expr -> IOThrowsError Expr) -> Expr
triop f = prim ["x", "y", "z"] $ \args -> f (args!"x") (args!"y") (args!"z")

triop' :: (Expr -> Expr -> Expr -> EnvStack -> IOThrowsError (Expr,EnvStack)) -> Expr
triop' f = prim' ["x", "y", "z"] $ \args -> f (args!"x") (args!"y") (args!"z")

primUnop :: (PrimData -> IOThrowsError Expr) -> Expr
primUnop f = prim ["x"] $ \args -> case args!"x" of
  EObj (PrimObj prim _) -> f prim
  x -> throwError $ "Invalid argument to primUnop: " ++ prettyPrint x

objUnop :: (Obj -> IOThrowsError Expr) -> Expr
objUnop f = prim ["x"] $ \args -> case args!"x" of
  EObj obj -> f obj
  x -> throwError $ "Invalid argument to objUnop: " ++ prettyPrint x

objUnop' :: (Obj -> EnvStack -> IOThrowsError (Expr,EnvStack)) -> Expr
objUnop' f = prim' ["x"] $ \args env -> case args!"x" of
  EObj obj -> f obj env
  x -> throwError $ "Invalid argument to objUnop': " ++ prettyPrint x

stringUnop :: (String -> IOThrowsError Expr) -> Expr
stringUnop f = objUnop $ \obj -> case getString2' obj of
  Just str -> f str
  Nothing -> throwError $ "Invalid argument to stringUnop: " ++ prettyPrint obj

stringUnop' :: (String -> EnvStack -> IOThrowsError (Expr,EnvStack)) -> Expr
stringUnop' f = objUnop' $ \obj env -> case getString2' obj of
  Just str -> f str env
  Nothing -> throwError $ "Invalid argument to stringUnop: " ++ prettyPrint obj

onNum :: (Integer -> Integer) -> (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onNum onInt onFloat (PInt b) = pure . makeInt $ onInt b
onNum onInt onFloat (PFloat b) = pure . makeFloat $ onFloat b
onNum onInt onFloat _ = throwError "Invalid argument to onNum"

onInt :: (Integer -> Integer) -> (PrimData -> IOThrowsError Expr)
onInt onInt (PInt b) = pure . makeInt $ onInt b
onInt onInt _ = throwError "Invalid argument to onInt"

onInt' :: (Integer -> IOThrowsError Expr) -> (PrimData -> IOThrowsError Expr)
onInt' f (PInt b) = f b
onInt' f _ = throwError "Invalid argument to onInt'"

onFloat :: (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onFloat onFloat (PInt b) = pure . makeFloat $ onFloat (fromInteger b)
onFloat onFloat (PFloat b) = pure . makeFloat $ onFloat b
onFloat onFloat _ = throwError "Invalid argument to onFloat"

onFloatOnly :: (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onFloatOnly onFloat (PFloat b) = pure . makeFloat $ onFloat b
onFloatOnly onFloat _ = throwError "Invalid argument to onFloatOnly"

onNumToBool :: (Integer -> Bool) -> (Double -> Bool) -> (PrimData -> IOThrowsError Expr)
onNumToBool onInt onFloat (PInt b) = pure . makeBool $ onInt b
onNumToBool onInt onFloat (PFloat b) = pure . makeBool $ onFloat b
onNumToBool onInt onFloat _ = throwError "Invalid argument to onNumToBool"

onFloatToBool :: (Double -> Bool)  -> (PrimData -> IOThrowsError Expr)
onFloatToBool onFloat (PInt b) = pure . makeBool $ onFloat (fromInteger b)
onFloatToBool onFloat (PFloat b) = pure . makeBool $ onFloat b
onFloatToBool onFloat _ = throwError "Invalid argument to onFloatToBool"

onBool :: (Bool -> Bool) -> (PrimData -> IOThrowsError Expr)
onBool f (PBool b) = pure . makeBool $ f b
onBool f _ = throwError "Invalid argument to onBool"
