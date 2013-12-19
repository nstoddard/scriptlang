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
import Data.Foldable (asum, toList)
import Debug.Trace
import System.Process

import Util

import Expr



isNilop (EClosure xs _ _) = all isNilop' xs
isNilop (EPrim xs _) = all isNilop' xs
isNilop _ = False

isNilop' (OptParam {}) = True
isNilop' (RepParam {}) = True
isNilop' _ = False

evalID derefVars (EId (id,accessType)) notFoundMsg env = do
  val <- envLookup id env
  case val of
    Nothing -> throwError $ notFoundMsg ++ id
    Just (val, accessType2) -> do
      (val,env) <- case (accessType,accessType2) of
        (ByVal, ByVal) -> pure (val,env)
        (ByVal, ByName) -> eval val env
        (ByName, ByName) -> pure (val,env)
        (ByName, ByVal) -> throwError $ "Invalid use of ~: " ++ prettyPrint val
      if derefVars then (case val of
        EVar var -> (,env) <$> lift (get var)
        val -> pure (val,env))
      else pure (val,env)

eval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
eval EVoid env = pure (EVoid, env)
eval id@(EId {}) env = evalID True id "Identifier not found: " env
eval (EGetVar var) env = evalID False (EId var) "Variable not found: " env
eval (EMemberAccess obj id) env = do
  obj <- eval obj env
  case obj of
    (EObj (Obj oenv),_) -> do
      (val,_) <- evalID True (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (EObj (PrimObj prim oenv),_) -> do
      (val,_) <- evalID True (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (x,_) -> throwError $ "Can't access member " ++ id ++ " on non-objects."
eval (EMemberAccessGetVar obj id) env = do
  obj <- eval obj env
  case obj of
    (EObj (Obj oenv),_) -> do
      (val,_) <- evalID False (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (EObj (PrimObj prim oenv),_) -> do
      (val,_) <- evalID False (eId id) "Object has no such field: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (x,_) -> throwError $ "Can't access member " ++ id ++ " on non-objects."
eval (EDef id val) env = envDefine id env $ do
  val <- (,ByVal) . fst <$> eval val env
  pure (val, fst val)
eval (EObj obj) env = pure (EObj obj, env)
eval (EBlock []) env = pure (EVoid, env)
eval (EBlock exprs) env = do
  env' <- envNewScope env
  vals <- forM exprs $ \expr -> eval expr env'
  pure (fst $ last vals, env)
eval (EFn params body) env = do
  verifyParams params
  pure (EClosure params body env, env)
eval (EFnApp fn args) env = do
  (fn',_) <- eval fn env
  case fn' of
    EClosure params body closure -> do
      verifyArgs args
      args' <- matchParams params args env
      bodyEnv <- envNewScope closure
      forM_ args' $ \(name,accessType,val) -> envDefine name bodyEnv (pure ((val,accessType),val))
      (res,_) <- eval body bodyEnv
      pure (res,env)
    EPrim params fn' -> do
      verifyArgs args
      args' <- matchParams params args env
      bodyEnv <- envNewScope =<< lift newEnvStack
      forM_ args' $ \(name,accessType,val) -> envDefine name bodyEnv (pure ((val,accessType),val))
      (res,_) <- fn' bodyEnv
      pure (res,env)
    EObj obj -> case args of
      [] -> pure (EObj obj,env) --This is the case when you have a lone identifier
      args'@(Arg (EId (id,ByVal)):args) -> do
        val <- envLookup id env
        case val of
          Just val -> evalApply obj args' env
          Nothing -> case args of
            args -> eval (EFnApp (EMemberAccess (EObj obj) id) args) env
      args -> evalApply obj args env
    EVoid -> case args of
      [] -> pure (EVoid,env)
      args -> throwError ("Invalid function: " ++ prettyPrint EVoid)
    x -> throwError ("Invalid function: " ++ prettyPrint x)
eval prim@(EPrim {}) env = pure (prim, env) --This is necessary for evaulating lists and tuples; it should never happen in any other case; TODO: can this be removed?
eval closure@(EClosure {}) env = pure (closure,env)--throwError "Can't evaluate closures; this should never happen"
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
eval (EVarDef id val) env = envDefine id env $ do
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
eval (EValClosure expr closure) env = (,env) . fst <$> eval expr closure
eval x _ = throwError $ "eval unimplemented for " ++ show x

--Like regular eval, but allows you to redefine things
replEval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
replEval (EDef id val) env = do
  (val',_) <- eval val env
  envRedefine id (val',ByVal) env
replEval (EVarDef id val) env = do
  (val',_) <- eval val env
  val'' <- lift $ EVar <$> newIORef val'
  envRedefine id (val'',ByVal) env
replEval expr env = eval expr env

call obj f args = eval (EFnApp (EMemberAccess (EObj obj) f) args)
evalApply obj args = eval (EFnApp (EMemberAccess (EObj obj) "apply") args)


matchArg :: Bool -> String -> AccessType -> Expr -> EnvStack -> IOThrowsError (String,AccessType,Expr)
matchArg evaluate name accessType arg env = do
  (arg',_) <- case accessType of
    ByVal -> if evaluate then eval arg env else pure (EValClosure arg env,env)
    ByName -> case arg of
      (EId (_,ByName)) -> if evaluate then eval arg env else pure (EValClosure arg env,env) --We must evaluate in this case or we end up trying to treat an identifier as a value when calling a function with something prefixed with ~, as occurs in "while"
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
  listArgs <- getList =<< fst <$> eval xs env
  matchParams params (ListArgNoEval listArgs:args) env
matchParams (OptParam (name,accessType) def:params) [] env = (:) <$> matchArg True name accessType def env <*> matchParams params [] env
matchParams [RepParam (name,accessType)] args env = do
  args <- concat <$> (forM args $ \arg -> case arg of
    Arg arg -> (:[]) . fst <$> eval arg env
    ListArg xs -> getList =<< fst <$> eval xs env
    ListArgNoEval args -> pure args
    KeywordArg k arg -> throwError $ "Can't pass keyword argument to repeated parameter: " ++ prettyPrint k ++ ":" ++ prettyPrint arg)
  pure [(name, accessType, makeList args)]
matchParams params_ (KeywordArg k arg:args) env = do
  params <- takeKeywordArg params_ k
  matchParams' params arg args True env
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


verifyParams :: [Param] -> IOThrowsError ()
verifyParams = verifyParams' S.empty where
  verifyParams' :: Set String -> [Param] -> IOThrowsError ()
  verifyParams' set [] = pure ()
  verifyParams' set (ReqParam name:  params) = verifyID set name params
  verifyParams' set (OptParam name _:params) = verifyID set name params
  verifyParams' set (RepParam name:  params) = verifyID set name params
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
  verifyArgs' set (RestArgs:args) = error "RestArgs in verifyArgs'"


envLookup' name env = fst <$> eval (EId (name,ByVal)) env


makeInt a = EObj $ PrimObj (PInt a) $ envFromList [
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
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("&&", primUnop $ onBool (a&&)),
  ("||", primUnop $ onBool (a||))
  ]
makeString a = EObj $ PrimObj (PString a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("apply", primUnop $ onInt' (\i -> makeChar <$> index a i))
  ]
makeList a = EObj $ PrimObj (PList a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("head", nilop $ if null a then throwError "Can't take the head of an empty list" else pure (head a)),
  ("tail", nilop $ if null a then throwError "Can't take the tail of an empty list" else pure (makeList $ tail a)),
  ("init", nilop $ if null a then throwError "Can't take the init of an empty list" else pure (makeList $ init a)),
  ("last", nilop $ if null a then throwError "Can't take the last of an empty list" else pure (last a)),
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("::", unop $ \b -> pure $ makeList (b:a)),
  ("apply", primUnop $ onInt' (index a))
  ]
makeTuple a = EObj $ PrimObj (PTuple a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("apply", primUnop $ onInt' (index a))
  ]

getList (EObj (PrimObj (PList xs) _)) = pure xs
getList x = throwError $ "Not a list: " ++ prettyPrint x

--These functions are necessary so that "(x,y)" evaluates its arguments before creating the tuple/list/whatever
makeList' xs = EFnApp makeListPrim (map Arg xs)
makeTuple' xs = EFnApp makeTuplePrim (map Arg xs)

makeListPrim = EPrim [repParam "xs"] (\env -> (,env) . makeList . fromEList <$> envLookup' "xs" env)
makeTuplePrim = EPrim [repParam "xs"] (\env -> (,env) . makeTuple . fromEList <$> envLookup' "xs" env)

index :: [a] -> Integer -> IOThrowsError a
index xs i = if i >= 0 && i < genericLength xs then pure (xs `genericIndex` i) else throwError "Invalid index!"



prim :: [String] -> (Map String Expr -> IOThrowsError Expr) -> Expr
prim args f = EPrim (map reqParam args) $ \env -> (,env) <$> (f =<< M.fromList <$> mapM (\arg -> (arg,) <$> envLookup' arg env) args)

prim' :: [String] -> (Map String Expr -> EnvStack -> IOThrowsError Expr) -> Expr
prim' args f = EPrim (map reqParam args) $ \env -> (,env) <$> (flip f env =<< M.fromList <$> mapM (\arg -> (arg,) <$> envLookup' arg env) args)

nilop :: IOThrowsError Expr -> Expr
nilop ret = prim [] (const ret)

nilop' :: (EnvStack -> IOThrowsError Expr) -> Expr
nilop' ret = prim' [] (\map env -> ret env)

floatNilop = nilop . pure . makeFloat

unop :: (Expr -> IOThrowsError Expr) -> Expr
unop f = prim ["x"] $ \args -> f (args!"x")

unop' :: (Expr -> EnvStack -> IOThrowsError Expr) -> Expr
unop' f = prim' ["x"] $ \args -> f (args!"x")

binop :: (Expr -> Expr -> IOThrowsError Expr) -> Expr
binop f = prim ["x", "y"] $ \args -> f (args!"x") (args!"y")

primUnop :: (PrimData -> IOThrowsError Expr) -> Expr
primUnop f = prim ["x"] $ \args -> let EObj (PrimObj prim _) = args!"x" in f prim

objUnop :: (Obj -> IOThrowsError Expr) -> Expr
objUnop f = prim ["x"] $ \args -> let EObj obj = args!"x" in f obj

objUnop' :: (Obj -> EnvStack -> IOThrowsError Expr) -> Expr
objUnop' f = prim' ["x"] $ \args env -> case args!"x" of
  EObj obj -> f obj env
  _ -> throwError "Invalid argument to objUnop'"

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
