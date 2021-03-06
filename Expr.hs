{-# LANGUAGE TupleSections, FlexibleContexts, FlexibleInstances #-}

module Expr where

import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Error
import Data.Maybe
import Data.Char
import System.IO
import System.IO.Unsafe
import System.IO.Error
import Control.Exception hiding (try)
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
import Control.Concurrent.BoundedChan

import qualified Text.PrettyPrint.Leijen as P
import Text.PrettyPrint.Leijen ((<//>), (</>), Pretty, pretty, displayS, renderPretty)

import Util hiding ((</>))

--- Environments ---

type Identifier = (String,AccessType)
type Value = (Expr,AccessType)

type Env = Map String Value
data EnvStack = EnvStack [IORef Env]


type UnitList = [UnitDef]
type UnitMap = Map String NumUnits

-- TODO: is there a good way to do this without making it global?
data GlobalEnv = GlobalEnv {
  envUnits :: UnitList,
  -- TODO: is this needed?
  envUnitNames :: [String],
  envUnitMap :: UnitMap
} deriving (Show)

{-# NOINLINE globalEnv #-}
globalEnv :: IORef GlobalEnv
globalEnv = unsafePerformIO $ newIORef $ GlobalEnv [] [] M.empty

getEnvs :: EnvStack -> IO [Env]
getEnvs (EnvStack []) = pure []
getEnvs (EnvStack (env:envs)) = (:) <$> get env <*> getEnvs (EnvStack envs)

envStackFromEnv :: Env -> IO EnvStack
envStackFromEnv env = (EnvStack . (:[])) <$> newIORef env

envFromList :: [(String,Expr)] -> Env
envFromList = M.fromList . map (second (,ByVal))

envStackFromList :: [(String,Expr)] -> IO EnvStack
envStackFromList xs = (EnvStack . (:[])) <$> newIORef (envFromList xs)

newEnvStack :: IO EnvStack
newEnvStack = (EnvStack . (:[])) <$> newIORef M.empty

envNewScope :: EnvStack -> IOThrowsError EnvStack
envNewScope (EnvStack xs) = do
  newScope <- lift $ newIORef M.empty
  pure (EnvStack (newScope:xs))

envTail :: EnvStack -> IOThrowsError EnvStack
envTail (EnvStack []) = throwError "Can't drop empty EnvStack!"
envTail (EnvStack (_:xs)) = pure $ EnvStack xs

envHead :: EnvStack -> IOThrowsError Env
envHead (EnvStack []) = throwError "Can't drop empty EnvStack!"
envHead (EnvStack (x:_)) = lift (get x)



--The third parameter isn't just a Value because it should only be executed if there isn't an error.
envDefine :: String -> EnvStack -> IOThrowsError (Value,Expr) -> IOThrowsError (Expr,EnvStack)
envDefine id env@(EnvStack (x:xs)) f = do
  x' <- lift $ get x
  (val,ret) <- f
  lift $ x $= M.insert id val x'
  pure (ret, env)
envDefine _ _ _ = error "Invalid arguments to envDefine"



--- Expressions ---

-- Units
type Power = Double
type Unit = String
type Units = Map Unit Power
type NumUnits = (Double, Units) -- A number, with units

data UnitType = UNormal | USI | UBin deriving (Show)

data UnitDef = UnitDef {
    unitType :: UnitType,
    unitNames :: [String],
    unitAbbrs :: [String],
    unitValue :: Maybe NumUnits
} deriving (Show) 
 


prettyUnit (unit, 1) = pretty unit
prettyUnit (unit, n) = pretty unit <//> pretty "^" <//> pretty n

prettyUnits units
    | not (null pos) && length neg == 1 = P.hsep (map prettyUnit pos) <//>
        pretty "/" <//> prettyUnit (second negate $ head neg)
    | otherwise = P.hsep (map prettyUnit units)
    where
        (pos, neg) = partition ((>0).snd) units

instance Pretty Units where
    pretty units
        | M.null units = pretty "(unitless)"
        | otherwise = prettyUnits (M.toList units)



data PrimData = PFloat Double Units | PBool Bool | PChar Char | PList [Expr] |
  PGen (IORef (Maybe Expr)) (BoundedChan (Maybe Expr)) | PHandle Handle String | PVoid


instance Clone Expr where
  clone (EVar var) = EVar <$> cloneIORef var
  clone x = pure x


data Expr =
  -- An identifier. Includes an access type as well.
  EId Identifier |
  -- An identifier, but doesn't dereference variables so they can be assigned to
  EGetVar Identifier |
  -- A function application. Note that these are created all the time; even the expression "5" will create a function application with no arguments. This is to support behavior like "5 meters" translating to "5 * meters".
  EFnApp Expr [Arg] |
  -- A variable definition. Overwrites any existing variable with the same name, in the same scope.
  EDef String Expr |
  -- A variable assignment. Only assigns to existing variables; will NOT create a new variable.
  EAssign Expr Expr |
  -- Something like "a.x"
  EMemberAccess Expr String |
  -- ???
  EVar (IORef Expr) |
  -- ???
  EMemberAccessGetVar Expr String |
  -- A compound expression like "(x = 5; x <- 10; x)"
  EBlock [Expr] |
  -- Object syntax like "{a = 5; b = 10}"
  EMakeObj [Expr] |
  -- The "new" operation
  ENew' [Expr] |
  -- The "clone" operation
  EClone Expr |
  -- Any type of object; could be a primitive like numbers, a user-defined object, or a function (yes, functions are represented as objects).
  EObj Obj |
  -- ???
  EValClosure Expr EnvStack |
  -- If statements
  EIf Expr Expr Expr |
  -- Unit definitions
  EUnitDef UnitType [String] [String] (Maybe Expr) |
  -- &'ls -a'
  ERunRawExternal String |
  -- &ls
  EExternalProgram String |
  -- &('ls')
  EEvalExternalProgram Expr |
  -- The "_" in (_+2)
  EUnknown

-- Determines whether an Expr should be saved to defs.txt
isStmt :: Expr -> Bool
isStmt (EDef {}) = True
isStmt (EAssign {}) = True
isStmt (EUnitDef {}) = True
isStmt _ = False

fromEList :: Expr -> [Expr]
fromEList (EObj (PrimObj (PList xs) _)) = xs
fromEList xs = error $ "Internal error: not a list: " ++ show xs

getVar :: Expr -> Maybe Expr
getVar (EId id) = pure $ EGetVar id
getVar (EMemberAccess expr id) = pure $ EMemberAccessGetVar expr id
getVar (EFnApp f []) = getVar f
getVar _ = Nothing

getExprEnv :: Expr -> IOThrowsError EnvStack
getExprEnv (EObj (Obj env)) = lift $ envStackFromEnv env
getExprEnv (EObj (PrimObj _ env)) = lift $ envStackFromEnv env
getExprEnv (EObj (FnObj _ (Closure _ env) _)) = pure env
getExprEnv x = throwError $ "No environment for: " ++ show x

-- ByVal is the normal mode. ByName is stuff like "~a" which doesn't eval the parameter until it's used. See "while" in stdlib.txt for an example.
data AccessType = ByVal | ByName deriving (Eq,Show)

--When a FnObj is called, it looks in the Env to see if it can handle the message. If so, it does. If not, it actually calls the function.
data Obj = Obj Env | PrimObj PrimData Env | FnObj [Param] Fn Env

class Clone a where
  -- |Copies all IORefs
  clone :: a -> IO a

instance Clone (Map String Value) where
  clone = mapM (\(expr, accessType) -> (,accessType) <$> clone expr)

instance Clone Obj where
  clone (Obj env) = Obj <$> clone env
  clone (PrimObj a b) = PrimObj a <$> clone b
  clone (FnObj a b c) = FnObj a b <$> clone c

-- This data structure stores only the body of the function. The parameter list is stored in FnObj, above.
data Fn =
  -- A primitive function
  Prim (EnvStack -> IOThrowsError (Expr,EnvStack)) |
  -- A user-defined function.
  Fn Expr |
  -- A closure; includes an environment
  Closure Expr EnvStack

--TODO: should I rename RepParam to ListParam for consistency with ListArg?
data Param =
  -- A normal parameter
  ReqParam Identifier |
  -- An optional parameter. Used like "?x=5 -> x"
  OptParam Identifier Expr |
  -- A repeated parameter
  RepParam Identifier deriving Show

data Arg =
  Arg Expr | KeywordArg String Expr | ListArg Expr | ListArgNoEval [Expr] | RestArgs | FlagArg String | LongFlagArg String deriving Show

type IOThrowsError = ErrorT String IO

reqParam name = ReqParam (name,ByVal)
optParam name = OptParam (name,ByVal)
repParam name = RepParam (name,ByVal)

eId name = EId (name,ByVal)


--- Pretty printer ---

outputToString doc = displayS (renderPretty 1.0 72 doc) ""
prettyPrint :: Pretty a => a -> String
prettyPrint = outputToString . pretty

-- |Like P.hsep, but with </> instead of <+>
hsep :: [P.Doc] -> P.Doc
hsep [] = P.empty
hsep [x] = x
hsep (x:xs) = x </> hsep xs

prettyBlock start end [] = pretty start P.<$> pretty end
prettyBlock start end xs = pretty start P.<$> P.indent 2 (P.vcat (map pretty xs)) P.<$> pretty end

prettyList xs = pretty "[" <//> P.cat (P.punctuate P.comma $ map pretty xs) <//> pretty "]"

instance Pretty AccessType where
  pretty ByVal = pretty ""
  pretty ByName = pretty "~"

instance Pretty Param where
  pretty (ReqParam (id,accessType)) = pretty accessType <//> pretty id
  pretty (OptParam (id,accessType) def) = pretty accessType <//> pretty id <//> pretty ":" <//> pretty def
  pretty (RepParam (id,accessType)) = pretty accessType <//> pretty id <//> pretty "*"

instance Pretty Arg where
  pretty (Arg expr) = pretty expr
  pretty (KeywordArg name expr) = pretty name <//> pretty ":" <//> pretty expr
  pretty (ListArg expr) = pretty expr <//> pretty "*"
  pretty (ListArgNoEval exprs) = pretty exprs <//> pretty "*"
  pretty (FlagArg flag) = pretty "`" <//> pretty flag

instance Pretty Expr where
  pretty (EId (id,accessType)) = pretty accessType <//> pretty id
  pretty (EFnApp f []) = pretty "(" <//> pretty f <//> pretty ")"
  pretty (EFnApp f args) = pretty "(" <//> pretty f </> hsep (map pretty args) <//> pretty ")"
  pretty (EMemberAccess obj id) = if isOperator id
    then pretty obj </> pretty id
    else pretty obj <//> pretty "." <//> pretty id
  pretty (EDef id val) = pretty id </> pretty "=" </> pretty val
  pretty (EAssign var val) = pretty var </> pretty "<-" </> pretty val
  pretty (EBlock xs) = prettyBlock '(' ')' xs
  pretty (EMakeObj xs) = prettyBlock '{' '}' xs
  pretty (ENew' xs) = pretty "(" <//> pretty "new" </> hsep (map pretty xs) <//> pretty ")"
  pretty (EClone x) = pretty "clone" </> pretty x
  pretty (EObj obj) = pretty obj
  pretty (EIf cond t f) = pretty "(if" </> pretty cond </> pretty t </> pretty "else" </> pretty f <//> pretty ")"
  pretty (EVar _) = pretty "<var>"
  pretty (EGetVar id) = pretty "<getVar>"
  pretty (EMemberAccessGetVar {}) = pretty "<memberAccessGetVar>"
  pretty EUnknown = pretty "_"
  pretty (EValClosure expr env) = pretty expr
  pretty x = pretty (show x) -- TODO

instance Pretty Fn where
  pretty (Prim _) = pretty "<prim>"
  pretty (Fn body) = pretty body
  pretty (Closure body env) = pretty body

instance Show PrimData where
  show (PFloat x xUnits) = show (x, xUnits) -- TODO
  show (PBool x) = show x
  show (PChar x) = show x
  show (PList xs) = show xs
  show (PGen {}) = show "<gen>"
  show (PHandle handle file) = show "<handle to " ++ file ++ ">"

instance Pretty PrimData where
  pretty (PFloat num units)
    | units == M.empty = pretty num
    | otherwise = pretty num </> prettyUnits (M.toList units)
  pretty (PBool True) = pretty "true"
  pretty (PBool False) = pretty "false"
  pretty (PChar x) = pretty '#' <//> pretty x
  pretty (PList xs) = case getString3' xs of
    Just str -> pretty '"' <//> pretty str <//> pretty '"'
    Nothing -> prettyList xs
  pretty (PGen {}) = pretty "<generator>"
  pretty (PHandle handle file) = pretty "<handle to" </> pretty file <//> pretty ">"


getList (EObj (PrimObj (PList xs) _)) = pure xs
getList x = throwError $ "Not a list: " ++ prettyPrint x

getChar' (EObj (PrimObj (PChar c) _)) = Just c
getChar' _ = Nothing

getString' (EObj (PrimObj (PList xs) _)) = let chars = mapMaybe getChar' xs in
  if length chars == length xs then Just chars else Nothing
getString' _ = Nothing

getString2' (PrimObj (PList xs) _) = let chars = mapMaybe getChar' xs in
  if length chars == length xs then Just chars else Nothing
getString2' _ = Nothing

getString3' xs = let chars = mapMaybe getChar' xs in
  if length chars == length xs then Just chars else Nothing



instance Pretty Obj where
  pretty (Obj _) = pretty "<object>"
  pretty (PrimObj prim _) = pretty prim
  pretty (FnObj params fn _) = pretty "(" <//> hsep (map pretty params) </> pretty "=>" </> pretty fn <//> pretty ")"


--This can't be derived automatically because of EnvStack
instance Show Obj where
  show (Obj _) = "Obj _"
  show (PrimObj prim _) = "(" ++ show prim ++ ")"
  show (FnObj params fn _) = "(EFn " ++ show params ++ " " ++ show fn ++ ")"

instance Show Fn where
  show (Prim _)  = "<prim>"
  show (Fn body) = show body
  show (Closure body env) = "<closure of: " ++ show body ++ ")"
  

--This can't be derived automatically because of EPrim
instance Show Expr where
  show (EId x)             = "(EId " ++ show x ++ ")"
  show (EFnApp x xs)       = "(EFnApp " ++ show x ++ " " ++ show xs ++ " " ++ ")"
  show (EMemberAccess x y) = "(EMemberAccess " ++ show x ++ " " ++ show y ++ ")"
  show (EDef a b)          = "(EDef " ++ show a ++ " " ++ show b ++ ")"
  show (EAssign a b)       = "(EAssign " ++ show a ++ " " ++ show b ++ ")"
  show (EVar _)            = "(EVar _)"
  show (EGetVar id)        = "(EGetVar " ++ show id ++ ")"
  show (EMemberAccessGetVar a b) = "(EMemberAccessGetVar " ++ show a ++ " " ++ show b ++ ")"
  show (EBlock xs)         = "(EBlock " ++ show xs ++ ")"
  show (EMakeObj x)        = "(EMakeObj " ++ show x ++ ")"
  show (ENew' x)           = "(ENew' " ++ unwords (map show x) ++ ")"
  show (EClone x)          = "(EClone " ++ show x ++ ")"
  show (EObj x)            = "(EOBj " ++ show x ++ ")"
  show (EIf cond t f)      = "(EIf " ++ show cond ++ " " ++ show t ++ " " ++ show f ++ ")"
  show EUnknown            = "EUnknown"
  show (EUnitDef a b c d)  = "(EUnitDef " ++ show a ++ " " ++ show b ++ " " ++ show c ++ " " ++ show d ++ ")"
  show (ERunRawExternal str) = "(ERunRawExternal " ++ show str ++ ")"
  show (EExternalProgram str) = "(EExternalProgram " ++ show str ++ ")"
  show (EEvalExternalProgram x) = "(EEvalExternalProgram " ++ show x ++ ")"


isOperator = not . isAlphaNum . head


getBool (EObj (PrimObj (PBool True) _)) = pure True
getBool (EObj (PrimObj (PBool False) _)) = pure False
getBool x = throwError $ "Not a bool: " ++ prettyPrint x
