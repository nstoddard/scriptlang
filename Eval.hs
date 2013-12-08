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
import System.Exit
import System.Directory
import qualified System.IO.Strict as Strict
import Data.Foldable (asum, toList)
import Debug.Trace
import System.Process

import Util

import Expr


evalID derefVars (EId (id,accessType)) notFoundMsg env = do
  val <- envLookup id env
  case val of
    Nothing -> throwError $ notFoundMsg ++ id
    Just (closure@(EClosure [] _ _), accessType2) -> eval closure env --TODO: what do we do with the access type here?
    Just (prim@(EPrim [] fn), accessType2) -> eval prim env --TODO: what do we do with the access type here?
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
      (val,_) <- evalID True (eId id) ("Object has no such field: ") =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (EObj (PrimObj prim oenv),_) -> do
      (val,_) <- evalID True (eId id) ("Object has no such field: ") =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (x,_) -> throwError $ "Can't access member " ++ id ++ " on non-objects."
eval (EMemberAccessGetVar obj id) env = do
  obj <- eval obj env
  case obj of
    (EObj (Obj oenv),_) -> do
      (val,_) <- evalID False (eId id) ("Object has no such field: ") =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (EObj (PrimObj prim oenv),_) -> do
      (val,_) <- evalID False (eId id) ("Object has no such field: ") =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (x,_) -> throwError $ "Can't access member " ++ id ++ " on non-objects."
eval (EDef id val) env = envDefine id env $ (,ByVal) . fst <$> eval val env
eval (EObj obj) env = pure (EObj obj, env)
eval (EBlock []) env = pure (EVoid, env)
eval (EBlock exprs) env = do
  env' <- envNewScope env
  vals <- forM exprs $ \expr -> eval expr env'
  pure (fst $ last vals, env)
eval (EFn params body) env = pure (EClosure params body env, env)
eval (EFnApp fn args) env = do
  (fn',_) <- eval fn env
  case fn' of
    EClosure params body closure -> do
      args' <- matchParams params args env
      bodyEnv <- envNewScope closure
      forM_ args' $ \(name,accessType,val) -> envDefine name bodyEnv (pure (val,accessType))
      (res,_) <- eval body bodyEnv
      pure (res,env)
    EPrim params fn -> do
      args' <- matchParams params args env
      bodyEnv <- envNewScope =<< lift newEnvStack
      forM_ args' $ \(name,accessType,val) -> envDefine name bodyEnv (pure (val,accessType))
      (res,_) <- fn bodyEnv
      pure (res,env)
    EObj obj -> case args of
      args'@(Arg (EId (id,ByVal)):args) -> do
        val <- envLookup id env
        case val of
          Just val -> evalApply obj args' env
          Nothing -> case args of
            [] -> eval (EMemberAccess (EObj obj) id) env
            args -> eval (EFnApp (EMemberAccess (EObj obj) id) args) env
      args -> evalApply obj args env
    x -> throwError ("Invalid function: " ++ show x)
eval (EPrim [] fn) env = do
  bodyEnv <- envNewScope =<< lift newEnvStack
  (res,_) <- fn bodyEnv
  pure (res,env)
eval prim@(EPrim {}) env = pure (prim, env) --This is necessary for evaulating lists and tuples; it should never happen in any other case
eval (EClosure [] body closure) env = do
  bodyEnv <- envNewScope closure
  (res,_) <- eval body bodyEnv
  pure (res,env)
eval (EClosure {}) env = throwError "Can't evaluate closures; this should never happen"
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
    c -> throwError $ "Invalid condition for if: " ++ show c
eval (EVarDef id val) env = envDefine id env $ do
  (val,_) <- eval val env
  lift $ (,ByVal) . EVar <$> newIORef val
eval (EAssign var val) env = do
  (var,_) <- eval var env
  (val',_) <- eval val env
  case var of
    EVar var -> lift $ var $= val'
    x -> throwError $ "Not a variable: " ++ show x
  pure (val', env)
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


evalApply obj args = eval (EFnApp (EMemberAccess (EObj obj) "apply") args)

--Don't forget to evaluate the arguments too!
matchParams :: [Param] -> [Arg] -> EnvStack -> IOThrowsError [(String,AccessType,Expr)]
matchParams [] [] _ = pure []
matchParams (ReqParam (name,accessType):params) (Arg arg:args) env = (:) <$> evalArg name accessType arg env <*> matchParams params args env
matchParams [RepParam (name,accessType)] args env = do
  args <- forM args $ \arg -> case arg of
    Arg arg -> fst <$> eval arg env
    _ -> throwError $ "Invalid argument for repeated parameter " ++ name
  pure [(name, accessType, makeList args)]
matchParams params arg env = throwError $ "matchParams unimplemented for " ++ show (params,arg)


evalArg :: String -> AccessType -> Expr -> EnvStack -> IOThrowsError (String,AccessType,Expr)
evalArg name accessType arg env = do
  (arg',_) <- case accessType of
    ByVal -> eval arg env
    ByName -> pure (arg, env)
  pure (name,accessType,arg')



envLookup' name env = fst <$> eval (EId (name,ByVal)) env


startEnv :: IO EnvStack
startEnv = envStackFromList [
  ("-", primUnop $ onNum negate negate),
  ("!", primUnop $ onBool not),
  ("exit", nilop (lift exitSuccess)),
  ("exec", EPrim [reqParam "proc", repParam "args"] $ \env -> do
    proc <- envLookup' "proc" env
    args <- envLookup' "args" env
    case (proc, args) of
      (EObj (PrimObj (PString proc) _), EObj (PrimObj (PList args) _)) -> do
        args <- forM args $ \arg -> case arg of
          EObj (PrimObj (PString arg) _) -> pure arg
          _ -> throwError "Invalid argument to exec"
        lift $ rawSystem proc args
        pure (EVoid, env)
      _ -> throwError "Invalid argument to exec"),
  ("execRaw", EPrim [reqParam "proc"] $ \env -> do
    proc <- envLookup' "proc" env
    case proc of
      (EObj (PrimObj (PString proc) _)) -> do
        lift $ system proc
        pure (EVoid, env)
      _ -> throwError "Invalid argument to execRaw"),
  ("env", nilop' $ \env -> lift (print =<< getEnv env) *> pure EVoid), --TODO: THIS DOESN'T WORK
  ("envOf", unop $ \expr -> (lift . (print <=< getEnv) =<< getExprEnv expr) *> pure EVoid)
  ]

makeInt a = EObj $ PrimObj (PInt a) $ envFromList [
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
  ("sign", nilop $ pure (makeInt $ signum a))
  ]
makeFloat a = EObj $ PrimObj (PFloat a) $ envFromList [
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
  ("abs", nilop $ pure (makeFloat $ abs a)),
  ("sign", nilop $ pure (makeFloat $ signum a))
  ]
makeChar a = EObj $ PrimObj (PChar a) $ envFromList []
makeBool a = EObj $ PrimObj (PBool a) $ envFromList [
  ("&&", primUnop $ onBool (a&&)),
  ("||", primUnop $ onBool (a||))
  ]
makeString a = EObj $ PrimObj (PString a) $ envFromList [
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("apply", primUnop $ onInt' (\i -> makeChar <$> index a i))
  ]
makeList a = EObj $ PrimObj (PList a) $ envFromList [
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
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("apply", primUnop $ onInt' (index a))
  ]

--These functions are necessary so that "(x,y)" evaluates its arguments before creating the tuple/list/whatever
makeList' = EFnApp makeListPrim . map Arg
makeTuple' = EFnApp makeTuplePrim . map Arg

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

unop :: (Expr -> IOThrowsError Expr) -> Expr
unop f = prim ["x"] $ \args -> f (args!"x")

binop :: (Expr -> Expr -> IOThrowsError Expr) -> Expr
binop f = prim ["x", "y"] $ \args -> f (args!"x") (args!"y")

primUnop :: (PrimData -> IOThrowsError Expr) -> Expr
primUnop f = prim ["x"] $ \args -> let EObj (PrimObj prim _) = args!"x" in f prim


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
