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
import System.IO.Error
import Control.Exception hiding (try)
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
import Control.Concurrent.BoundedChan as B

import Util hiding (try)

import Expr


isNilop (EObj (FnObj params _ _)) = all isNilop' params
isNilop _ = False

isNilop' (OptParam {}) = True
isNilop' (RepParam {}) = True
isNilop' _ = False

evalID derefVars (EId (id,accessType)) notFoundMsg env = do
  val <- envLookup id env
  case val of
    EnvNotFound -> throwError $ notFoundMsg ++ id
    EnvFoundUnit (EObj (PrimObj (PFloat num units) _)) -> do
      unitEnv <- get globalEnv
      pure (uncurry makeFloat (num,units))
    EnvFound (val, accessType2) -> do
      val <- case (accessType,accessType2) of
        (ByVal, ByVal) -> pure val
        (ByVal, ByName) -> eval' val env
        (ByName, ByName) -> pure val
        (ByName, ByVal) -> throwError $ "Invalid use of ~: " ++ prettyPrint val
      if derefVars then (case val of
        EVar var -> lift (get var)
        val -> pure val)
      else pure val

lookupID id = evalID True (EId (id,ByVal)) "Identifier not found: "

--Similar to rawSystem, but also handles commands like "sbt" and "clear"
myRawSystem command args = system (intercalate " " $ map parenify (command:args))
  where parenify str = if any isSpace str then "\"" ++ str ++ "\"" else str



data EnvResult = EnvFound Value | EnvFoundUnit Expr | EnvNotFound
  deriving (Show)

envLookup :: String -> EnvStack -> IOThrowsError EnvResult
envLookup id (EnvStack []) = do
  unitEnv <- get globalEnv
  if id `elem` envUnitNames unitEnv then do
    let (num,units) = (1.0, M.singleton id 1.0)
    pure $ EnvFoundUnit $ makeFloat num units
  else pure EnvNotFound
envLookup id (EnvStack (x:xs)) = do
  x' <- lift $ get x
  case M.lookup id x' of
    Nothing -> envLookup id (EnvStack xs)
    Just res -> pure (EnvFound res)





eval :: Expr -> EnvStack -> IOThrowsError (Expr, EnvStack)
eval id@(EId _) env =
  (,env) <$> evalID True id "Unknown identifier: " env
eval (EGetVar var) env =
  (,env) <$> evalID False (EId var) "Variable not found: " env
eval (EMemberAccess obj id) env = do
  obj <- eval' obj env
  case obj of
    EObj (Obj oenv) -> do
      val <- evalID True (eId id) "Object has no such field in member access: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    EObj (PrimObj prim oenv) -> do
      val <- evalID True (eId id) "Object has no such field in member access: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    x -> throwError $ "Can't access member " ++ id ++ " on non-object: " ++ prettyPrint x
eval (EMemberAccessGetVar obj id) env = do
  obj <- eval' obj env
  case obj of
    EObj (Obj oenv) -> do
      val <- evalID False (eId id) "Object has no such field in member access 2: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    EObj (PrimObj prim oenv) -> do
      val <- evalID False (eId id) "Object has no such field in member access 2: " =<< lift (envStackFromEnv oenv)
      pure (val, env)
    x -> throwError $ "Can't access member " ++ id ++ " on non-object: " ++ prettyPrint x
eval (EObj (FnObj params (Fn body) fnEnv)) env = do
  verifyParams params
  pure (EObj (FnObj params (Closure body env) fnEnv), env)
eval prim@(EObj (FnObj _ (Prim _) _)) env = pure (prim, env) --This is necessary for evaulating lists; it should never happen in any other case; TODO: can this be removed?
eval closure@(EObj (FnObj _ (Closure _ _) _)) env = pure (closure,env) --TODO: this used to give an error but is now enabled; why?
eval (EObj obj) env = pure (EObj obj, env)
eval (EBlock []) env = pure (makeVoid, env)
eval (EBlock exprs) env = do
  env' <- envNewScope env
  vals <- forM exprs $ \expr -> eval expr env'
  pure (fst $ last vals, env)
eval (EFnApp fn args) env = do
  (fn,_) <- eval fn env
  case fn of
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
            EnvFound (val,ByVal) -> eval (EFnApp val args) env
            EnvFoundUnit val -> evalFnApp
            EnvNotFound -> evalFnApp
        _ -> evalFnApp
    EObj obj -> case args of
      [] -> pure (EObj obj,env) --This is the case when you have a lone identifier. It's not a function.
      args'@(Arg (EId (id,ByVal)):args) -> do
        val <- envLookup id env
        case val of
          EnvFound val -> evalApply obj args' env
          EnvFoundUnit val -> evalApply obj args' env
          EnvNotFound -> eval (EFnApp (EMemberAccess (EObj obj) id) args) env
      args -> evalApply obj args env
      --args -> throwError ("Invalid function: " ++ prettyPrint (EObj obj))
    EExternalProgram prog -> do
      verifyArgs args
      args' <- getExecArgs args env
      res <- lift $ tryJust (guard . isDoesNotExistError) (myRawSystem prog args')
      case res of
        Left err -> throwError $ "Program not found: " ++ prog
        Right res -> pure (makeVoid, env)
    x -> throwError ("Invalid function: " ++ prettyPrint x)
eval (EMakeObj exprs) env = do
  env' <- envNewScope env
  forM_ exprs $ \expr -> eval expr env'
  obj <- envHead env'
  pure (EObj (Obj obj), env)
eval (EClone x) env = do
  (x',_) <- eval x env
  case x' of
    EObj (Obj obj) -> (,env) . EObj . Obj <$> lift (clone obj)
    _ -> throwError "Invalid argument to clone; must be an object."
eval (ENew' xs) env = do
  xs' <- mapM (`eval` env) xs
  foldM (\(res, env) (x,_) -> case (res, x) of
    (EObj (Obj res), EObj (Obj obj)) -> do
      obj' <- lift (clone obj)
      -- In the union, obj' must come before res because M.union is left-biased
      pure (EObj . Obj $ M.union obj' res, env)
    _ -> throwError "Invalid argument to 'new'; must be an object."
    ) (EObj (Obj M.empty), env) xs'
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
eval (EUnitDef utype names abbrs expr) env = do
    val <- case expr of
        Nothing -> pure Nothing
        Just expr -> Just <$> eval' expr env
    val' <- case val of
        Just (EObj (PrimObj (PFloat num units) _)) -> pure $ Just (num, units)
        Nothing -> pure Nothing
        x -> do
          lift $ putStrLn $ "Can't define a unit with the value " ++ prettyPrint x
          pure Nothing
    let
        unitDef = UnitDef {unitType = utype,
            unitNames = names, unitAbbrs = abbrs, unitValue = val'}
    lift $ mapM addUnitDef (addSIPrefixes unitDef)
    pure (makeVoid, env)
eval (ERunRawExternal program) env = do
  res <- lift $ tryJust (guard . isDoesNotExistError) (system program)
  case res of
    Left err -> throwError $ "Program not found: " ++ program
    Right res -> pure (makeVoid, env)
eval (EExternalProgram prog) env = pure (EExternalProgram prog, env)
eval (EEvalExternalProgram expr) env = do
  res <- getString' <$> eval' expr env
  case res of
    Just str -> pure (EExternalProgram str, env)
    Nothing -> throwError $ "Not a valid program: " ++ show res


addUnitDef unitDef = do
  env <- get globalEnv
  -- TODO: don't silently ignore this
  if unitExists env unitDef then pure () {-putStrLn ("Unit already exists: " ++ show unitDef-} {-++ "; " ++ show env-}{-)-} else do
  globalEnv $= env {
    envUnits = unitDef : envUnits env,
    envUnitNames = unitNames unitDef ++ unitAbbrs unitDef ++ envUnitNames env,
    envUnitMap = case unitValue unitDef of
      Nothing -> envUnitMap env
      Just value -> M.fromList (map (, value) (unitNames unitDef ++ unitAbbrs unitDef)) `M.union` envUnitMap env
    }

unitExists env unitDef = any (`elem` envUnitNames env) (unitNames unitDef ++ unitAbbrs unitDef)

toBaseUnits :: UnitList -> UnitMap -> NumUnits -> NumUnits
toBaseUnits unitList m (n, units) = M.foldl'
    (\(aN, aUnits) (bN, bUnits) -> (aN*bN, combineUnits aUnits bUnits))
    (n, M.empty) (M.mapWithKey toBaseUnits' units) where
    toBaseUnits' :: Unit -> Power -> NumUnits
    toBaseUnits' unit power = case M.lookup unit m of
        Nothing -> (1.0, M.singleton unit' power) where
            unit' = head . unitNames $ fromJust
                (find (\x -> unit `elem` unitNames x || unit `elem` unitAbbrs x) unitList)
        Just res -> toBaseUnits unitList m (((**power) *** M.map (*power)) res)


validUnit :: Units -> IO Bool
validUnit units = do
  unitEnv <- get globalEnv
  pure $ all (`elem` envUnitNames unitEnv) (map fst $ M.toList units)


convertUnits :: UnitList -> UnitMap -> NumUnits -> Units -> IOThrowsError NumUnits
convertUnits unitList m a b
    | aUnits == bUnits = pure (aRes*recip bRes, b)
    | otherwise = throwError $ "Invalid unit conversion from " ++
        prettyPrint aUnits ++ " to " ++ prettyPrint b ++ "."
    where
    (aRes, aUnits) = toBaseUnits unitList m a
    (bRes, bUnits) = toBaseUnits unitList m (1.0, b)

combineUnits :: Units -> Units -> Units
combineUnits = M.mergeWithKey (\_ a b -> if a+b==0 then Nothing else Just (a+b)) id id

addSIPrefixes unitDef = case unitType unitDef of
    USI -> unitDef : map addSIPrefixes' siPrefixes
    UBin -> unitDef : map addSIPrefixes' siPrefixes ++ map addSIPrefixes' binPrefixes
    UNormal -> [unitDef]
    where
        addSIPrefixes' (prefix, shortPrefix, mul) = UnitDef {
            unitType = UNormal,
            unitNames = (prefix++) <$> unitNames unitDef,
            unitAbbrs = (shortPrefix++) <$> unitAbbrs unitDef,
            unitValue = Just (mul, M.singleton (head $ unitNames unitDef) 1.0)
        }

siPrefixes = [
    ("yotta", "Y", 1000**8),
    ("zetta", "Z", 1000**7),
    ("exa"  , "E", 1000**6),
    ("peta" , "P", 1000**5),
    ("tera" , "T", 1000**4),
    ("giga" , "G", 1000**3),
    ("mega" , "M", 1000**2),
    ("kilo" , "k", 1000**1),
    ("hecto", "h", 100),
    ("deca" , "da", 10),

    ("deci" , "d", 0.1),
    ("centi", "c", 0.01),
    ("milli", "m", 1000**(-1)),
    ("micro", "mu",1000**(-2)),
    ("nano" , "n", 1000**(-3)),
    ("pico" , "p", 1000**(-4)),
    ("femto", "f", 1000**(-5)),
    ("atto" , "a", 1000**(-6)),
    ("zepto", "z", 1000**(-7)),
    ("yocto", "y", 1000**(-8))
    ]
binPrefixes = [
    ("yobi", "Yi", 1024**8),
    ("zebi", "Zi", 1024**7),
    ("exbi", "Ei", 1024**6),
    ("pebi", "Pi", 1024**5),
    ("tebi", "Ti", 1024**4),
    ("gibi", "Gi", 1024**3),
    ("mebi", "Mi", 1024**2),
    ("kibi", "Ki", 1024**1)
    ]


apply f args = eval' (EFnApp f args)
call obj f args = eval' (EFnApp (EMemberAccess (EObj obj) f) args)
evalApply obj args = eval (EFnApp (EMemberAccess (EObj obj) "apply") args)

eval' expr env = fst <$> eval expr env

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
matchParams params@(ReqParam {}:_) (ListArgNoEval (arg:lArgs):args) env =
  matchParams' params arg (ListArgNoEval lArgs:args) False env
matchParams params@(OptParam {}:_) (ListArgNoEval (arg:lArgs):args) env =
  matchParams' params arg (ListArgNoEval lArgs:args) False env
matchParams params (ListArg xs:args) env = do
  listArgs <- getList =<< eval' xs env
  matchParams params (ListArgNoEval listArgs:args) env
matchParams (OptParam (name,accessType) def:params) [] env = (:) <$> matchArg True name accessType def env <*> matchParams params [] env
matchParams [RepParam (name,accessType)] args env = do
  args <- concat <$> forM args (\arg -> case arg of
    Arg arg -> (:[]) <$> eval' arg env
    ListArg xs -> getList =<< eval' xs env
    ListArgNoEval args -> pure args
    KeywordArg k arg -> throwError $ "Can't pass keyword argument to repeated parameter: " ++ prettyPrint k ++ ":" ++ prettyPrint arg)
  pure [(name, accessType, makeList args)]
matchParams params_ (KeywordArg k arg:args) env = do
  params <- takeKeywordArg params_ k
  matchParams' params arg args True env
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


envLookup' name = eval' (EId (name,ByVal))


makeInt a = makeFloat (fromIntegral a) M.empty

makeFloat :: Double -> Units -> Expr
makeFloat a aUnits = EObj $ PrimObj (PFloat a aUnits) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a)),
  ("+", primUnop $ onFloatSameUnits (+) a'),
  ("-", primUnop $ onFloatSameUnits (-) a'),
  ("*", primUnop $ onFloatCombineUnits combineUnits (*) a'),
  ("apply", primUnop $ onFloatCombineUnits combineUnits (*) a'),
  ("/", primUnop $ onFloatCombineUnits
    (\a b -> combineUnits a (negate <$> b)) (/) a'),
  ("div", primUnop $ onApproxIntUnitless (div) a'),
  ("^", primUnop $ power a'),
  ("==", primUnop $ onFloatToBoolSameUnits (==) a'),
  (">", primUnop $ onFloatToBoolSameUnits (>) a'),
  ("<", primUnop $ onFloatToBoolSameUnits (<) a'),
  (">=", primUnop $ onFloatToBoolSameUnits (>=) a'),
  ("<=", primUnop $ onFloatToBoolSameUnits (<=) a'),
  ("!=", primUnop $ onFloatToBoolSameUnits (/=) a'),
  ("@", primUnop $ \b -> case b of
    PFloat b bUnits -> do
      let b' = (b, bUnits)
      bValid <- lift $ validUnit (snd b')
      case (a', bValid) of
        (PFloat a aUnits, True) -> do
          unitEnv <- get globalEnv
          (num,units) <- convertUnits (envUnits unitEnv) (envUnitMap unitEnv) (a/fst b', aUnits) (snd b')
          pure $ makeFloat num units
        (PFloat a aUnits, False) -> throwError $
          "Invalid unit in convesion: " ++ prettyPrint b ++ "."
        (x, _) -> throwError $
            "Invalid conversion: can't convert " ++ prettyPrint x ++ "."
    _ -> error "Invalid arguments to @"),
  ("%", primUnop $ onFloatNoUnits2 fmod a'),
  ("abs", nilop $ onFloatWithUnits1 abs a'),
  ("sign", nilop $ onFloatWithUnits1 signum a'),
  ("floor", nilop $ onFloatNoUnits1 (fromIntegral . floor) a'),
  ("ceil", nilop $ onFloatNoUnits1 (fromIntegral . ceiling) a'),
  ("truncate", nilop $ onFloatNoUnits1 (fromIntegral . truncate) a'),
  ("round", nilop $ onFloatNoUnits1 (fromIntegral . round) a'),
  ("ln", nilop $ onFloatNoUnits1 log a'),
  ("log", nilop $ onFloatNoUnits1 (logBase 10) a'),
  ("lg", nilop $ onFloatNoUnits1 (logBase 2) a'),
  ("exp", nilop $ onFloatNoUnits1 exp a'),
  ("sqrt", nilop $ onFloatNoUnits1 sqrt a'),
  ("sin", nilop $ onFloatNoUnits1 sin a'),
  ("cos", nilop $ onFloatNoUnits1 cos a'),
  ("tan", nilop $ onFloatNoUnits1 tan a'),
  ("asin", nilop $ onFloatNoUnits1 asin a'),
  ("acos", nilop $ onFloatNoUnits1 acos a'),
  ("atan", nilop $ onFloatNoUnits1 atan a'),
  ("sinh", nilop $ onFloatNoUnits1 sinh a'),
  ("cosh", nilop $ onFloatNoUnits1 cosh a'),
  ("tanh", nilop $ onFloatNoUnits1 tanh a'),
  ("asinh", nilop $ onFloatNoUnits1 asinh a'),
  ("acosh", nilop $ onFloatNoUnits1 acosh a'),
  ("atanh", nilop $ onFloatNoUnits1 atanh a')
  {-("isNaN", nilop . pure . makeBool $ isNaN a),
  ("isInfinite", nilop . pure . makeBool $ isInfinite a),
  ("isDenormalized", nilop . pure . makeBool $ isDenormalized a),
  ("isNegativeZero", nilop . pure . makeBool $ isNegativeZero a),
  ("logBase", primUnop $ onFloat (logBase a)),
  ("atan2", primUnop $ onFloat (atan2 a)),
  ("through", primUnop $ \x -> case (asApproxInt a, asApproxInt' x) of
    (Just a, Just b) -> pure $ makeList $ map makeInt [a..b]
    _ -> throwError "Invalid argument to 'to'"),
  ("until", primUnop $ \x -> case (asApproxInt a, asApproxInt' x) of
    (Just a, Just b) -> pure $ makeList $ map makeInt [a..b-1]
    _ -> throwError "Invalid argument to 'to'"),
  ("gcd", primUnop $ onApproxInt (gcd) a),
  ("lcm", primUnop $ onApproxInt (lcm) a)-}
  ] where a' = PFloat a aUnits

onApproxIntUnitless :: (Integer -> Integer -> Integer) -> PrimData -> (PrimData -> IOThrowsError Expr)
onApproxIntUnitless f (PFloat a aUnits) (PFloat b bUnits) = case (asApproxInt a, asApproxInt b) of
  (Just a, Just b) -> if M.null aUnits && M.null bUnits
    then pure . makeInt $ f a b
    else throwError "Invalid argument to onInt"
  _ -> throwError "Invalid argument to onInt"


-- If the double is approximately an integer, rounds it. Otherwise, returns Nothing.
asApproxInt :: Double -> Maybe Integer
asApproxInt x
  | abs (fromIntegral x' - x) < 1e-9 = Just x'
  | otherwise = Nothing
  where x' = round x

{-asApproxInt' (PFloat x) = asApproxInt x
asApproxInt' _ = Nothing-}

makeVoid = EObj $ PrimObj PVoid $ envFromList []

makeChar a = EObj $ PrimObj (PChar a) $ envFromList [
  ("toString", nilop $ pure (makeString $ prettyPrint a))
  ]

makeBool a = EObj $ PrimObj (PBool a) $ envFromList [
  ("toString", nilop $ pure (makeString $ if a then "true" else "false")),
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
  --("length", nilop $ pure (makeInt $ fromIntegral $ length a)),
  ("::", unop $ \b -> pure $ makeList (b:a)),
  ("++", primUnop $ \x -> case x of
    PList b -> pure $ makeList (a++b)
    _ -> throwError "Invalid argument to ++"),
  --("apply", primUnop $ onInt' (index a)),
  ("map", unop' $ \fn env -> (,env) . makeList <$> mapM (flip (apply fn) env . (:[]) . Arg) a),
  ("filter", unop' $ \fn env -> (,env) . makeList <$> filterM (getBool <=< flip (apply fn) env . (:[]) . Arg) a)
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
      val <- lift $ B.readChan chan
      lift $ writeIORef ioRef val
      let gotOne = isJust val
      lift $ writeIORef done (not gotOne)
      pure (makeBool gotOne))
    ]

makeHandle handle file = EObj $ PrimObj (PHandle handle file) $ envFromList [
  ("atEOF", nilop $ makeBool <$> lift (hIsEOF handle)),
  ("readChar", nilop $ do
    eof <- lift $ hIsEOF handle
    if eof then pure makeVoid else makeChar <$> lift (hGetChar handle)),
  ("writeChar", objUnop $ \obj -> case obj of
    PrimObj (PChar char) _ -> do
      lift $ hPutChar handle char
      pure makeVoid
    _ -> throwError $ "Invalid argument to writeChar: " ++ prettyPrint obj)
  ]


--These functions are necessary so that "(x,y)" evaluates its arguments before creating the list
makeList' xs = EFnApp makeListPrim (map Arg xs)

makeListPrim = ePrim [repParam "xs"] (\env -> (,env) . makeList . fromEList <$> envLookup' "xs" env)

index :: [a] -> Integer -> IOThrowsError a
index xs i = if i >= 0 && i < genericLength xs then pure (xs `genericIndex` i) else throwError "Invalid index!"



--TODO: turn this into a type class?
desugar :: Expr -> Expr
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
desugar (EMakeObj xs) = EMakeObj (map desugar xs)
desugar (ENew' xs) = ENew' (map desugar xs)
desugar (EClone x) = EClone (desugar x)
desugar (EObj x) = EObj $ desugarObj x
desugar (EIf a b c) = EIf (desugar a) (desugar b) (desugar c)
desugar EUnknown = EUnknown
desugar (EUnitDef a b c x) = EUnitDef a b c (desugar <$> x)
desugar (ERunRawExternal x) = ERunRawExternal x
desugar (EExternalProgram x) = EExternalProgram x
desugar (EEvalExternalProgram x) = EEvalExternalProgram (desugar x)

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

--floatNilop = nilop . pure . makeFloat

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

onNum :: (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onNum onFloat (PFloat b bUnits) = pure $ makeFloat (onFloat b) bUnits
onNum onFloat _ = throwError "Invalid argument to onNum"

{-onInt' :: (Integer -> IOThrowsError Expr) -> (PrimData -> IOThrowsError Expr)
onInt' f (PFloat b) = case asApproxInt b of
  Just b -> f b
  _ -> throwError "Invalid argument to onInt'"
onInt' f _ = throwError "Invalid argument to onInt'"

onFloat :: (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onFloat onFloat (PFloat b) = pure . makeFloat $ onFloat b
onFloat onFloat _ = throwError "Invalid argument to onFloat"-}

convertPFloat (PFloat x xUnits) yUnits = do
  unitEnv <- get globalEnv
  (num,units) <- convertUnits (envUnits unitEnv) (envUnitMap unitEnv) (x, xUnits) yUnits
  pure $ PFloat num units
convertPFloat _ _ = error "Invalid argument to convertPFloat"


exprEq :: Expr -> Expr -> IOThrowsError Bool
exprEq (EId a) (EId b) = pure (a==b)
exprEq (EObj a) (EObj b) = objEq a b
exprEq _ _ = pure False

objEq :: Obj -> Obj -> IOThrowsError Bool
objEq (PrimObj a ae) (PrimObj b be) = case (a, b) of
  (PVoid, PVoid) -> pure True
  (PFloat a aUnits, b@(PFloat {})) -> do
    PFloat b bUnits <- convertPFloat b aUnits
    pure (a==b && aUnits==bUnits)
  (PBool a, PBool b) -> pure (a==b)
  (PChar a, PChar b) -> pure (a==b)
  (PList as, PList bs) -> if length as == length bs
    then and <$> zipWithM exprEq as bs
    else pure False
  (_,_) -> pure False
objEq _ _ = pure False


onFloatToBoolSameUnits :: (Double -> Double -> Bool) -> PrimData -> (PrimData -> IOThrowsError Expr)
onFloatToBoolSameUnits onFloat (PFloat a aUnits) b = do
  PFloat b bUnits <- convertPFloat b aUnits
  if aUnits == bUnits then pure . makeBool $ onFloat a b
  else throwError "Invalid argument to onFloatToBool"
onFloatToBoolSameUnits onFloat _ _ = throwError "Invalid argument to onFloatToBool"

onBool :: (Bool -> Bool) -> (PrimData -> IOThrowsError Expr)
onBool f (PBool b) = pure . makeBool $ f b
onBool f _ = throwError "Invalid argument to onBool"


onFloatSameUnits :: (Double -> Double -> Double) -> PrimData -> (PrimData -> IOThrowsError Expr)
onFloatSameUnits f (PFloat a aUnits) b = do
  PFloat b bUnits <- convertPFloat b aUnits
  if aUnits == bUnits then pure $ makeFloat (f a b) aUnits
  else throwError "Incompatible units"
onFloatSameUnits _ _ _ = throwError "Invalid argument to onFloatSameUnits"

onFloatNoUnits1 :: (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onFloatNoUnits1 f (PFloat a aUnits) = do
  if aUnits == M.empty then pure $ makeFloat (f a) aUnits
  else throwError "Incompatible units"
onFloatNoUnits1 _ _ = throwError "Invalid argument to onFloatNoUnits1"

onFloatWithUnits1 :: (Double -> Double) -> (PrimData -> IOThrowsError Expr)
onFloatWithUnits1 f (PFloat a aUnits) = do
  pure $ makeFloat (f a) aUnits
onFloatWithUnits1 _ _ = throwError "Invalid argument to onFloatWithUnits1"

onFloatNoUnits2 :: (Double -> Double -> Double) -> PrimData -> (PrimData -> IOThrowsError Expr)
onFloatNoUnits2 f (PFloat a aUnits) (PFloat b bUnits) = do
  if aUnits == M.empty && bUnits == M.empty then pure $ makeFloat (f a b) aUnits
  else throwError "Incompatible units"
onFloatNoUnits2 _ _ _ = throwError "Invalid argument to onFloatNoUnits2"

onFloatCombineUnits :: (Units -> Units -> Units) -> (Double -> Double -> Double) -> PrimData -> (PrimData -> IOThrowsError Expr)
onFloatCombineUnits combine f (PFloat a aUnits) (PFloat b bUnits)
  = pure $ makeFloat (f a b) (combine aUnits bUnits)
onFloatCombineUnits _ _ _ _ = throwError "Invalid argument to onFloatCombineUnits"

power :: PrimData -> (PrimData -> IOThrowsError Expr)
power (PFloat b bUnits) (PFloat a aUnits)
  | M.null bUnits = pure $ makeFloat (a**b) (M.map (*b) aUnits)
  | otherwise = throwError "Incompatible units"
power _ _ = throwError "Invalid argument to power"
