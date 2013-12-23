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

envRedefine :: String -> Value -> EnvStack -> IOThrowsError (Expr,EnvStack)
envRedefine id val env@(EnvStack (x:xs)) = do
  x' <- lift $ get x
  lift $ x $= M.insert id val x'
  pure (fst val, env)

envRemoveIORefs :: EnvStack -> IO [Map String Value]
envRemoveIORefs (EnvStack xs) = mapM get xs




--- Expressions ---

data PrimData = PInt Integer | PFloat Double | PBool Bool | PChar Char | PString String | PList [Expr] | PTuple [Expr] deriving Show

data Expr =
  EVoid |
  EId Identifier | EFnApp Expr [Arg] | EMemberAccess Expr String |
  EPrim [Param] (EnvStack -> IOThrowsError (Expr,EnvStack)) | EFn [Param] Expr |
  EExec String [String] |
  EDef String Expr | EVarDef String Expr | EAssign Expr Expr | EVar (IORef Expr) | EGetVar Identifier | EMemberAccessGetVar Expr String |
  EBlock [Expr] | ENew [Expr] | EWith Expr Expr |
  EObj Obj |
  EClosure [Param] Expr EnvStack | EValClosure Expr EnvStack |
  EIf Expr Expr Expr |
  EUnknown

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
getExprEnv (EClosure _ _ env) = pure env
getExprEnv x = throwError $ "No environment for: " ++ show x

data AccessType = ByVal | ByName deriving (Eq,Show)

data Obj = Obj Env | PrimObj PrimData Env

--TODO: should I rename RepParam to ListParam for consistency with ListArg?
data Param = ReqParam Identifier | OptParam Identifier Expr | RepParam Identifier | FlagParam String deriving Show
data Arg = Arg Expr | KeywordArg String Expr | ListArg Expr | ListArgNoEval [Expr] | RestArgs | FlagArg String deriving Show

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
  pretty (EFnApp f []) = pretty f
  pretty (EFnApp f args) = pretty "(" <//> pretty f </> hsep (map pretty args) <//> pretty ")"
  pretty (EMemberAccess obj id) = if isOperator id
    then pretty obj </> pretty id
    else pretty obj <//> pretty "." <//> pretty id
  pretty (EPrim _ _) = pretty "<prim>"
  pretty (EFn params body) = pretty "(" <//> hsep (map pretty params) </> pretty "=>" </> pretty body <//> pretty ")"
  pretty (EDef id val) = pretty id </> pretty "=" </> pretty val
  pretty (EVarDef id val) = pretty "var" </> pretty id </> pretty "<-" </> pretty val
  pretty (EAssign var val) = pretty var </> pretty "<-" </> pretty val
  pretty (EBlock xs) = prettyBlock xs
  pretty (ENew xs) = pretty "(" <//> pretty "new" </> prettyBlock xs <//> pretty ")"
  pretty (EWith a b) = pretty a </> pretty "with" </> pretty b
  pretty (EObj obj) = pretty obj
  pretty (EClosure params body env) = pretty (EFn params body)
  pretty (EIf cond t f) = pretty "(if" </> pretty cond </> pretty t </> pretty "else" </> pretty f <//> pretty ")"
  pretty (EVar _) = pretty "<var>"
  pretty (EGetVar id) = pretty "<getVar>"
  pretty (EMemberAccessGetVar {}) = pretty "<memberAccessGetVar>"
  pretty EUnknown = pretty "_"
  pretty (EValClosure expr env) = pretty expr
  pretty (EExec prog args) = pretty prog </> hsep (map pretty args)

instance Pretty PrimData where
  pretty (PInt x) = pretty x
  pretty (PFloat x) = pretty x
  pretty (PBool True) = pretty "true"
  pretty (PBool False) = pretty "false"
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
  show (EFnApp x xs)       = "(EFnApp " ++ show x ++ " " ++ show xs ++ " " ++ ")"
  show (EMemberAccess x y) = "(EMemberAccess " ++ show x ++ " " ++ show y ++ ")"
  show (EPrim _ _)         = "(EPrim <prim>" ++ ")"
  show (EFn params body)   = "(EFn " ++ show params ++ " " ++ show body ++ ")"
  show (EDef a b)          = "(EDef " ++ show a ++ " " ++ show b ++ ")"
  show (EVarDef a b)       = "(EVarDef " ++ show a ++ " " ++ show b ++ ")"
  show (EAssign a b)       = "(EAssign " ++ show a ++ " " ++ show b ++ ")"
  show (EVar _)            = "(EVar _)"
  show (EGetVar id)        = "(EGetVar " ++ show id ++ ")"
  show (EMemberAccessGetVar a b) = "(EMemberAccessGetVar " ++ show a ++ " " ++ show b ++ ")"
  show (EBlock xs)         = "(EBlock " ++ show xs ++ ")"
  show (ENew x)            = "(ENew " ++ show x ++ ")"
  show (EWith a b)         = "(EWith " ++ show a ++ " " ++ show b ++ ")"
  show (EObj x)            = "(EOBj " ++ show x ++ ")"
  show (EClosure a b env)  = "(EClosure " ++ show a ++ " " ++ show b ++ " " ++ "<env>" ++ ")"
  show (EIf cond t f)      = "(EIf " ++ show cond ++ " " ++ show t ++ " " ++ show f ++ ")"
  show EUnknown            = "EUnknown"


isOperator = not . isAlphaNum . head


getBool (EObj (PrimObj (PBool True) _)) = pure True
getBool (EObj (PrimObj (PBool False) _)) = pure False
getBool x = throwError $ "Not a bool: " ++ prettyPrint x


desugar :: Expr -> Expr
desugar EVoid = EVoid
desugar (EId id) = EId id
desugar (EFnApp EUnknown []) = EUnknown
desugar (EFnApp fn args) = processUnknownArgs (desugar fn) (map desugarArg args)
desugar (EMemberAccess a b) = EMemberAccess (desugar a) b
desugar prim@(EPrim {}) = prim
desugar (EFn params body) = EFn (map desugarParam params) (desugar body)
desugar (EDef name val) = EDef name (desugar val)
desugar (EVarDef name val) = EVarDef name (desugar val)
desugar (EAssign a b) = EAssign (desugar a) (desugar b)
desugar (EVar _) = error "Can't have an EVar in desugar!"
desugar (EGetVar id) = EGetVar id
desugar (EMemberAccessGetVar a b) = EMemberAccessGetVar (desugar a) b
desugar (EBlock xs) = EBlock (map desugar xs)
desugar (ENew xs) = ENew (map desugar xs)
desugar (EWith a b) = EWith (desugar a) (desugar b)
desugar (EObj x) = EObj x
desugar (EClosure {}) = error "Can't have a closure in desugar!"
desugar (EIf a b c) = EIf (desugar a) (desugar b) (desugar c)
desugar EUnknown = EUnknown

processUnknownArgs :: Expr -> [Arg] -> Expr
--TODO: support the case where the fn is EMemberAccess and there's no params
processUnknownArgs (EMemberAccess obj field) [] = if isUnknown obj
  then EFn [reqParam "_a"] (EFnApp (EMemberAccess (eId "_a") field) [])
  else EFnApp (EMemberAccess obj field) []
processUnknownArgs fn [] = EFnApp fn []
--TODO: remove this code duplication
processUnknownArgs (EMemberAccess obj field) args = case (isUnknown obj, not (null unknowns), hasRestArgs) of
  (False,_,True) -> EFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp (EMemberAccess obj field) (replaceUnknowns args 0))
  (True,_,True) -> EFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp (EMemberAccess (eId "_a") field) (replaceUnknowns args 1))
  (True,_,False) -> EFn (map reqParam unknowns) (EFnApp (EMemberAccess (eId "_a") field) (replaceUnknowns args 1))
  (False,True,False) -> EFn (map reqParam unknowns) (EFnApp (EMemberAccess obj field) (replaceUnknowns args 0))
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
  (False,_,True) -> EFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp fn (replaceUnknowns args 0))
  (True,_,True) -> EFn (map reqParam unknowns ++ [repParam "_xs"]) (EFnApp (eId "_a") (replaceUnknowns args 1))
  (True,_,False) -> EFn (map reqParam unknowns) (EFnApp (eId "_a") (replaceUnknowns args 1))
  (False,True,False) -> EFn (map reqParam unknowns) (EFnApp fn (replaceUnknowns args 0))
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
