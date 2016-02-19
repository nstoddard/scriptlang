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
import Control.Concurrent.BoundedChan

import qualified Text.PrettyPrint.Leijen as P
import Text.PrettyPrint.Leijen ((<//>), (</>), Pretty, pretty, displayS, renderPretty)

import Util

--- Environments ---

type Identifier = (String,AccessType)
type Value = (Expr,AccessType)

type Env = Map String Value
data EnvStack = EnvStack [IORef Env]

getEnv :: EnvStack -> IO [Env]
getEnv (EnvStack []) = pure []
getEnv (EnvStack (env:envs)) = (:) <$> get env <*> getEnv (EnvStack envs)

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

envLookup :: String -> EnvStack -> IOThrowsError (Maybe Value)
envLookup id (EnvStack []) = pure Nothing
envLookup id (EnvStack (x:xs)) = do
  x' <- lift $ get x
  case M.lookup id x' of
    Nothing -> envLookup id (EnvStack xs)
    Just res -> pure (Just res)

--The third parameter isn't just a Value because it should only be executed if there isn't an error.
envDefine :: String -> EnvStack -> IOThrowsError (Value,Expr) -> IOThrowsError (Expr,EnvStack)
envDefine id env@(EnvStack (x:xs)) f = do
  x' <- lift $ get x
  case M.lookup id x' of
    Nothing -> do
      (val,ret) <- f
      lift $ x $= M.insert id val x'
      pure (ret, env)
    Just _ -> throwError $ "Can't reassign identifier: " ++ id

--The third parameter isn't just a Value because it should only be executed if there isn't an error.
envRedefine :: String -> EnvStack -> IOThrowsError (Value,Expr) -> IOThrowsError (Expr,EnvStack)
envRedefine id env@(EnvStack (x:xs)) f = do
  x' <- lift $ get x
  (val,ret) <- f
  lift $ x $= M.insert id val x'
  pure (ret, env)

envRemoveIORefs :: EnvStack -> IO [Map String Value]
envRemoveIORefs (EnvStack xs) = mapM get xs




--- Expressions ---

data PrimData = PInt Integer | PFloat Double | PBool Bool | PChar Char | PList [Expr] |
  PGen (IORef (Maybe Expr)) (BoundedChan (Maybe Expr)) | PHandle Handle String


instance Clone Expr where
  clone (EVar var) = EVar <$> cloneIORef var
  clone x = pure x


data Expr =
  EVoid |
  EId Identifier | EFnApp Expr [Arg] | EMemberAccess Expr String |
  EExec String [String] |
  EDef String Expr | EAssign Expr Expr | EVar (IORef Expr) | EGetVar Identifier | EMemberAccessGetVar Expr String |
  EBlock [Expr] | EMakeObj [Expr] | ENew' [Expr] | EClone Expr |
  EObj Obj |
  EValClosure Expr EnvStack |
  EIf Expr Expr Expr |
  EUnknown

exprEq :: Expr -> Expr -> IO Bool
exprEq EVoid EVoid = pure True
exprEq (EId a) (EId b) = pure (a==b)
exprEq (EObj a) (EObj b) = objEq a b
exprEq _ _ = pure False

objEq :: Obj -> Obj -> IO Bool
objEq (PrimObj a ae) (PrimObj b be) = case (a, b) of
  (PInt a, PInt b) -> pure (a==b)
  (PFloat a, PFloat b) -> pure (a==b)
  (PBool a, PBool b) -> pure (a==b)
  (PChar a, PChar b) -> pure (a==b)
  (PList as, PList bs) -> and <$> sequence (exprEq <$> as <*> bs)
  (_,_) -> pure False
objEq _ _ = pure False

fromEList :: Expr -> [Expr]
fromEList (EObj (PrimObj (PList xs) _)) = xs
fromEList xs = error $ "Internal error: not a list: " ++ show xs

getVar :: Expr -> Maybe Expr
getVar (EId id) = pure $ EGetVar id
getVar (EMemberAccess expr id) = pure $ EMemberAccessGetVar expr id
getVar (EFnApp f []) = getVar f --TODO: is this line still needed?
getVar _ = Nothing

getExprEnv :: Expr -> IOThrowsError EnvStack
getExprEnv (EObj (Obj env)) = lift $ envStackFromEnv env
getExprEnv (EObj (PrimObj _ env)) = lift $ envStackFromEnv env
getExprEnv (EObj (FnObj _ (Closure _ env) _)) = pure env
getExprEnv x = throwError $ "No environment for: " ++ show x

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

data Fn = Prim (EnvStack -> IOThrowsError (Expr,EnvStack)) | Fn Expr | Closure Expr EnvStack

--TODO: should I rename RepParam to ListParam for consistency with ListArg?
data Param = ReqParam Identifier | OptParam Identifier Expr | RepParam Identifier | FlagParam String deriving Show
data Arg = Arg Expr | KeywordArg String Expr | ListArg Expr | ListArgNoEval [Expr] | RestArgs | FlagArg String | LongFlagArg String deriving Show

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
  pretty (FlagParam flag) = pretty flag <//> pretty "?"

instance Pretty Arg where
  pretty (Arg expr) = pretty expr
  pretty (KeywordArg name expr) = pretty name <//> pretty ":" <//> pretty expr
  pretty (ListArg expr) = pretty expr <//> pretty "*"
  pretty (ListArgNoEval exprs) = pretty exprs <//> pretty "*"
  pretty (FlagArg flag) = pretty "`" <//> pretty flag

instance Pretty Expr where
  pretty EVoid = pretty "void"
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
  pretty (EExec prog args) = pretty prog </> hsep (map pretty args)

instance Pretty Fn where
  pretty (Prim _) = pretty "<prim>"
  pretty (Fn body) = pretty body
  pretty (Closure body env) = pretty body

instance Show PrimData where
  show (PInt x) = show x
  show (PFloat x) = show x
  show (PBool x) = show x
  show (PChar x) = show x
  show (PList xs) = show xs
  show (PGen {}) = show "<gen>"
  show (PHandle handle file) = show "<handle to " ++ file ++ ">"

instance Pretty PrimData where
  pretty (PInt x) = pretty x
  pretty (PFloat x) = pretty x
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
  show EVoid               = "(EVoid" ++ ")"
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


isOperator = not . isAlphaNum . head


getBool (EObj (PrimObj (PBool True) _)) = pure True
getBool (EObj (PrimObj (PBool False) _)) = pure False
getBool x = throwError $ "Not a bool: " ++ prettyPrint x
