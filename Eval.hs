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


evalID (EId (id,accessType)) notFoundMsg env = do
  val <- envLookup id env
  case val of
    Nothing -> throwError $ notFoundMsg ++ id
    Just (closure@(EClosure [] _ _), accessType2) -> eval closure env --TODO: what do we do with the access type here?
    Just (prim@(EPrim [] fn), accessType2) -> eval prim env --TODO: what do we do with the access type here?
    Just (val, accessType2) -> case (accessType,accessType2) of
      (ByVal, ByVal) -> pure (val,env)
      (ByVal, ByName) -> eval val env
      (ByName, ByName) -> pure (val,env)
      (ByName, ByVal) -> throwError $ "Invalid use of ~: " ++ prettyPrint val


eval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
eval EVoid env = pure (EVoid, env)
eval id@(EId {}) env = evalID id "Identifier not found: " env
eval (EMemberAccess obj id) env = do
  obj <- eval obj env
  case obj of
    (EObj (Obj oenv),_) -> do
      (val,_) <- evalID (eId id) ("Object has no such field: ") =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (EObj (PrimObj prim oenv),_) -> do
      (val,_) <- evalID (eId id) ("Object has no such field: ") =<< lift (envStackFromEnv oenv)
      pure (val, env)
    (x,_) -> throwError $ "Can't access member " ++ id ++ " on non-objects."
eval (EDef id val) env = do
  oldVal <- envLookup id env
  case oldVal of
    Nothing -> do
      (val',_) <- eval val env
      envDefine id (val',ByVal) env
      pure (EVoid, env)
    Just _ -> throwError ("Can't reassign variable " ++ id)
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
      forM_ args' $ \(name,accessType,val) -> envDefine name (val,accessType) bodyEnv
      (res,_) <- eval body bodyEnv
      pure (res,env)
    EPrim params fn -> do
      args' <- matchParams params args env
      bodyEnv <- envNewScope =<< lift newEnvStack
      forM_ args' $ \(name,accessType,val) -> envDefine name (val,accessType) bodyEnv
      (res,_) <- fn bodyEnv
      pure (res,env)
    EObj obj -> case args of
      args'@(Arg (EId (id,ByVal)):args) -> do
        val <- envLookup id env
        case val of
          Just val -> evalApply obj args' env
          Nothing -> eval (EFnApp (EMemberAccess (EObj obj) id) args) env
      args -> evalApply obj args env
    x -> throwError ("Invalid function: " ++ show x)
eval (EPrim [] fn) env = do
  bodyEnv <- envNewScope =<< lift newEnvStack
  (res,_) <- fn bodyEnv
  pure (res,env)
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
eval x _ = throwError $ "eval unimplemented for " ++ show x

--Like regular eval, but allows you to redefine things
replEval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
replEval (EDef id val) env = do
  (val',_) <- eval val env
  envRedefine id (val',ByVal) env
  pure (EVoid, env)
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
  ("-", primUnop $ intOnNum negate negate),
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
      _ -> throwError "Invalid argument to execRaw")
  ]


makeInt a = EObj $ PrimObj (PInt a) $ envFromList [
  ("+", primUnop $ intOnNum (a+) (fromInteger a+)),
  ("-", primUnop $ intOnNum (a-) (fromInteger a-)),
  ("*", primUnop $ intOnNum (a*) (fromInteger a*)),
  ("/", primUnop $ floatOnNum (fromInteger a/) (fromInteger a/)),
  ("%", primUnop $ intOnNum (mod a) (fmod (fromInteger a))),
  ("^", primUnop $ intOnNum (a^) (fromInteger a**)),
  ("div", primUnop $ intOnInt (a `div`)),
  ("gcd", primUnop $ intOnInt (a `gcd`)),
  ("lcm", primUnop $ intOnInt (a `lcm`)),
  (">", primUnop $ intOnNumToBool (a>) (fromInteger a>)),
  ("<", primUnop $ intOnNumToBool (a<) (fromInteger a<)),
  (">=", primUnop $ intOnNumToBool (a>=) (fromInteger a>=)),
  ("<=", primUnop $ intOnNumToBool (a<=) (fromInteger a<=)),
  ("==", primUnop $ intOnNumToBool (a==) (fromInteger a==)),
  ("!=", primUnop $ intOnNumToBool (a/=) (fromInteger a/=))
  ]
makeFloat a = EObj $ PrimObj (PFloat a) $ envFromList [
  ("+", primUnop $ floatOnNum (a+) (a+)),
  ("-", primUnop $ floatOnNum (a-) (a-)),
  ("*", primUnop $ floatOnNum (a*) (a*)),
  ("/", primUnop $ floatOnNum (a/) (a/)),
  ("%", primUnop $ floatOnNum (fmod a) (fmod a)),
  ("^", primUnop $ floatOnNum (a**) (a**)),
  (">", primUnop $ floatOnNumToBool (a>) (a>)),
  ("<", primUnop $ floatOnNumToBool (a<) (a<)),
  (">=", primUnop $ floatOnNumToBool (a>=) (a>=)),
  ("<=", primUnop $ floatOnNumToBool (a<=) (a<=)),
  ("==", primUnop $ floatOnNumToBool (a==) (a==)),
  ("!=", primUnop $ floatOnNumToBool (a/=) (a/=))
  ]
makeChar a = EObj $ PrimObj (PChar a) $ envFromList []
makeBool a = EObj $ PrimObj (PBool a) $ envFromList [
  ("&&", primUnop $ onBool (a&&)),
  ("||", primUnop $ onBool (a||))
  ]
makeString a = EObj $ PrimObj (PString a) $ envFromList [
  ("apply", primUnop $ onInt (\i -> makeChar <$> index a i))
  ]
makeList a = EObj $ PrimObj (PList a) $ envFromList [
  ("head", nilop $ if null a then throwError "Can't take the head of an empty list" else pure (head a)),
  ("tail", nilop $ if null a then throwError "Can't take the tail of an empty list" else pure (makeList $ tail a)),
  ("init", nilop $ if null a then throwError "Can't take the init of an empty list" else pure (makeList $ init a)),
  ("last", nilop $ if null a then throwError "Can't take the last of an empty list" else pure (last a)),
  ("empty", nilop $ pure (makeBool $ null a)),
  ("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("::", unop $ \b -> pure $ makeList (b:a)),
  ("apply", primUnop $ onInt (index a))
  ]
makeTuple a = EObj $ PrimObj (PTuple a) $ envFromList [
  ("apply", primUnop $ onInt (index a))
  ]

index :: [a] -> Integer -> IOThrowsError a
index xs i = if i >= 0 && i < genericLength xs then pure (xs `genericIndex` i) else throwError "Invalid index!"

prim :: [String] -> (Map String Expr -> IOThrowsError Expr) -> Expr
prim args f = EPrim (map reqParam args) $ \env -> (,env) <$> (f =<< M.fromList <$> mapM (\arg -> (arg,) <$> envLookup' arg env) args)

nilop ret = prim [] (const ret)

unop :: (Expr -> IOThrowsError Expr) -> Expr
unop f = prim ["b"] $ \args -> let b = args!"b" in f b

primUnop :: (PrimData -> IOThrowsError Expr) -> Expr
primUnop f = prim ["b"] $ \args -> let EObj (PrimObj prim _) = args!"b" in f prim

--TODO: fix this horrible naming scheme

intOnNum :: (Integer -> Integer) -> (Double -> Double) -> (PrimData -> IOThrowsError Expr)
intOnNum onInt onFloat (PInt b) = pure . makeInt $ onInt b
intOnNum onInt onFloat (PFloat b) = pure . makeFloat $ onFloat b
intOnNum onInt onFloat _ = throwError "Invalid argument to intOnNum"

intOnInt :: (Integer -> Integer) -> (PrimData -> IOThrowsError Expr)
intOnInt onInt (PInt b) = pure . makeInt $ onInt b
intOnInt onInt _ = throwError "Invalid argument to intOnInt"

onInt :: (Integer -> IOThrowsError Expr) -> (PrimData -> IOThrowsError Expr)
onInt f (PInt b) = f b
onInt f _ = throwError "Invalid argument to onInt"

--TODO: will the user EVER provide 2 different functions for this?
floatOnNum :: (Double -> Double) -> (Double -> Double) -> (PrimData -> IOThrowsError Expr)
floatOnNum onInt onFloat (PInt b) = pure . makeFloat $ onInt (fromInteger b)
floatOnNum onInt onFloat (PFloat b) = pure . makeFloat $ onFloat b
floatOnNum onInt onFloat _ = throwError "Invalid argument to floatOnNum"

intOnNumToBool :: (Integer -> Bool) -> (Double -> Bool) -> (PrimData -> IOThrowsError Expr)
intOnNumToBool onInt onFloat (PInt b) = pure . makeBool $ onInt b
intOnNumToBool onInt onFloat (PFloat b) = pure . makeBool $ onFloat b
intOnNumToBool onInt onFloat _ = throwError "Invalid argument to intOnNumToBool"

--TODO: will the user EVER provide 2 different functions for this?
floatOnNumToBool :: (Double -> Bool) -> (Double -> Bool) -> (PrimData -> IOThrowsError Expr)
floatOnNumToBool onInt onFloat (PInt b) = pure . makeBool $ onInt (fromInteger b)
floatOnNumToBool onInt onFloat (PFloat b) = pure . makeBool $ onFloat b
floatOnNumToBool onInt onFloat _ = throwError "Invalid argument to floatOnNumToBool"

onBool :: (Bool -> Bool) -> (PrimData -> IOThrowsError Expr)
onBool f (PBool b) = pure . makeBool $ f b
onBool f _ = throwError "Invalid argument to onBool"
