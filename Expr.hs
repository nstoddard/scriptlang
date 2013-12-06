{-# LANGUAGE TupleSections #-}

module Expr where

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

import qualified Text.PrettyPrint.Leijen as P
import Text.PrettyPrint.Leijen ((<//>), (</>), Pretty, pretty, displayS, renderPretty)

import Util

--- Environments ---

type Identifier = (String,AccessType)
type Value = (Expr,AccessType)

type Env = Map String Value
data EnvStack = EnvStack [IORef Env]

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

envDefine :: String -> Value -> EnvStack -> IOThrowsError ()
envDefine id val env@(EnvStack (x:xs)) = do
  x' <- lift $ get x
  case M.lookup id x' of
    Nothing -> lift $ x $= M.insert id val x'
    Just _ -> throwError $ "Can't reassign identifier: " ++ id

envRedefine :: String -> Value -> EnvStack -> IOThrowsError ()
envRedefine id val env@(EnvStack (x:xs)) = do
  x' <- lift $ get x
  lift $ x $= M.insert id val x'

envRemoveIORefs :: EnvStack -> IO [Map String Value]
envRemoveIORefs (EnvStack xs) = mapM get xs




--- Expressions ---

--TODO: statements and expressions should have separate types! They're handled separately in the parser, already.

data PrimData = PInt Integer | PFloat Double | PBool Bool | PChar Char | PString String | PList [Expr] | PTuple [Expr] deriving Show

data Expr =
  EVoid |
  EId Identifier | EFnApp Expr [Arg] | EMemberAccess Expr String |
  EPrim [Param] (EnvStack -> IOThrowsError (Expr,EnvStack)) | EFn [Param] Expr |
  EDef String Expr | EVarDef String Expr | EAssign Expr Expr |
  EBlock [Expr] | ENew [Expr] | EWith Expr Expr |
  EObj Obj |
  EClosure [Param] Expr EnvStack |
  EIf Expr Expr Expr

data AccessType = ByVal | ByName deriving (Eq,Show)

data Obj = Obj Env | PrimObj PrimData Env

data Param = ReqParam Identifier | OptParam Identifier Expr | RepParam Identifier deriving Show
data Arg = Arg Expr | KeywordArg String Expr deriving Show

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

prettyBlock [] = pretty "{" P.<$> pretty "}"
prettyBlock xs = pretty "{" P.<$> P.indent 2 (P.vcat (map pretty xs)) P.<$> pretty "}"

prettyList xs = pretty "[" <//> P.cat (P.punctuate P.comma $ map pretty xs) <//> pretty "]"
prettyTuple xs = pretty "(" <//> P.cat (P.punctuate P.comma $ map pretty xs) <//> pretty ")"

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

instance Pretty Expr where
  pretty EVoid = pretty "void"
  pretty (EId (id,accessType)) = pretty accessType <//> pretty id
  pretty (EFnApp f []) = pretty f
  pretty (EFnApp f args) = pretty "(" <//> pretty f </> hsep (map pretty args) <//> pretty ")"
  pretty (EMemberAccess obj id) = if isOperator id
    then pretty obj </> pretty id
    else pretty obj <//> pretty "." <//> pretty id
  pretty (EPrim _ _) = pretty "<prim>"
  pretty (EFn params body) = hsep (map pretty params) </> pretty "=>" </> pretty body
  pretty (EDef id val) = pretty id </> pretty "=" </> pretty val
  pretty (EVarDef id val) = pretty "var" </> pretty id </> pretty "<-" </> pretty val
  pretty (EAssign var val) = pretty var </> pretty "<-" </> pretty val
  pretty (EBlock xs) = prettyBlock xs
  pretty (ENew xs) = pretty "(" <//> pretty "new" </> prettyBlock xs <//> pretty ")"
  pretty (EWith a b) = pretty a </> pretty "with" </> pretty b
  pretty (EObj obj) = pretty obj
  pretty (EClosure {}) = pretty "<closure>"
  pretty (EIf cond t f) = pretty "(if" </> pretty cond </> pretty t </> pretty "else" </> pretty f <//> pretty ")"

instance Pretty PrimData where
  pretty (PInt x) = pretty x
  pretty (PFloat x) = pretty x
  pretty (PBool x) = pretty x
  pretty (PChar x) = pretty '#' <//> pretty x
  pretty (PString x) = pretty '"' <//> pretty x <//> pretty '"'
  pretty (PList xs) = prettyList xs
  pretty (PTuple xs) = prettyTuple xs



instance Pretty Obj where
  pretty (Obj _) = pretty "<object>"
  pretty (PrimObj prim _) = pretty prim


--This can't be derived automatically because of EnvStack
instance Show Obj where
  show (Obj _) = "Obj _"
  show (PrimObj prim _) = "(" ++ show prim ++ ")"

--This can't be derived automatically because of EPrim
instance Show Expr where
  show EVoid               = "(EVoid" ++ ")"
  show (EId x)             = "(EId " ++ show x ++ ")"
  show (EFnApp x xs)       = "(EFnApp " ++ show x ++ " " ++ show xs ++ ")"
  show (EMemberAccess x y) = "(EMemberAccess " ++ show x ++ " " ++ show y ++ ")"
  show (EPrim _ _)           = "(EPrim <prim>" ++ ")"
  show (EFn params body)   = "(EFn " ++ show params ++ " " ++ show body ++ ")"
  show (EDef a b)          = "(EDef " ++ show a ++ " " ++ show b ++ ")"
  show (EVarDef a b)       = "(EVarDef " ++ show a ++ " " ++ show b ++ ")"
  show (EAssign a b)       = "(EAssign " ++ show a ++ " " ++ show b ++ ")"
  show (EBlock xs)         = "(EBlock " ++ show xs ++ ")"
  show (ENew x)            = "(ENew " ++ show x ++ ")"
  show (EWith a b)         = "(EWith " ++ show a ++ " " ++ show b ++ ")"
  show (EObj x)            = "(EOBj " ++ show x ++ ")"
  show (EClosure a b c)    = "(EClosure " ++ show a ++ " " ++ show b ++ " " ++ "<env>" ++ ")"
  show (EIf cond t f)      = "(EIf " ++ show cond ++ " " ++ show t ++ " " ++ show f ++ ")"




isOperator = not . isAlphaNum . head
