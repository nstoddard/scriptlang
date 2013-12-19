{-# LANGUAGE TupleSections #-}

module Scriptlang where

{- TODO
  For current version:
    Map, filter, etc should be methods on lists, not functions
    More I/O
    Glob syntax and regexes
    Command history
    Interfacing between scripts - this should be fairly easy

  In later versions:
    Types and pattern matching
    Generators
    Syntax for specifying chars with a hex code
    Extension methods
    Data declarations
    Maps - perhaps I should hold off on implementing this until I've implemented pattern matching - it seems that pattern matching and maps could be combined to simplify the language - this is one thing that I find irritating about Scala; it's sometimes hard to decide which one to use
    Unit testing
    Reflection - checking which fields, methods, etc an object supportss
    Imports
    Flags - use ` as a prefix; ` is translated to - in the generated call to a command. key:val is translated to "--key val"
    Consider adding by-reference parameters - when passing a variable to it, instead of passing its value it would pass the variable itself
    Should it be possible to overload assignment?
    Add fields - like Scala's getters and setters
    Treat functions as objects with an "apply" method and "o" as a composition operator
    Make sure _ and especially _* work properly with by-name parameters.
    Function overloading
    Line numbers for errors
    Add a method to be called when a method isn't defined
    Cloning of objects?
    Get rid of EValClosure - it's only used for by-name parameters, so the two features can probably be merged

  Improve error messages
    Doing primitive operations on unsupported types, such as "3 + []"
    Improve parse errors

  Do by-name optional parameters make sense?
  Disallow ~ on everything but parameters - zero-argument functions have replaced them
-}

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
import Data.Map (Map)
import System.Exit
import System.Directory
import qualified System.IO.Strict as Strict
import Data.Foldable (asum, toList)
import Debug.Trace
import System.Process

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import Util

import Expr
import Parse
import Eval


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
  ("envOf", unop $ \expr -> (lift . (print <=< getEnv) =<< getExprEnv expr) *> pure EVoid),
  ("print", objUnop' $ \obj env -> do
    (expr,_) <- call obj "toString" [] env
    case expr of
      EObj (PrimObj (PString str) _) -> lift $ putStr str
      x -> throwError $ "toString must return a string; not " ++ prettyPrint x
    pure EVoid),
  ("println", objUnop' $ \obj env -> do
    (expr,_) <- call obj "toString" [] env
    case expr of
      EObj (PrimObj (PString str) _) -> lift $ putStrLn str
      x -> throwError $ "toString must return a string; not " ++ prettyPrint x
    pure EVoid),
  ("readln", nilop $ makeString <$> lift getLine),
  ("eval", objUnop' $ \obj env -> case obj of
    PrimObj (PString str) _ -> fst <$> parseEval str env
    x -> throwError $ "Can't evaluate non-string: " ++ prettyPrint x)
  ]

parseEval str env = do
  expr <- parseInput "" str parseExpr desugar
  eval expr env


main = do
  env <- startEnv
  env <- runErrorT $ runFile "stdlib" env
  case env of
    Left err -> putStrLn err
    Right env -> repl env



repl env = do
  input <- replGetInput Nothing
  expr_ <- runErrorT (parseInput "" input parseExpr desugar)
  case expr_ of
    Left err -> putStrLn err >> repl env
    Right expr -> do
      --print expr
      --putStrLn (prettyPrint expr)

      res <- runErrorT (replEval expr env)
      case res of
        Left err -> putStrLn err >> repl env
        Right (EVoid, env') -> repl env'
        Right (expr', env') -> do
          putStrLn (prettyPrint expr')
          repl env'

parseInput :: String -> String -> Parsec String () a -> (a->a) -> IOThrowsError a
parseInput srcName input parser desugar = case parse (parseWholeInput parser) srcName input of
  Left err -> throwError ("Syntax error " ++ show err)
  Right expr -> pure $ desugar expr

runFile :: String -> EnvStack -> IOThrowsError EnvStack
runFile filename env = do
  exists <- lift $ doesFileExist filename
  if not exists then throwError ("File doesn't exist: " ++ filename) else do
  input <- lift $ Strict.readFile filename
  exprs <- parseInput filename input parseCompound (map desugar)
  --lift $ putStrLn $ "Running file: " ++ filename
  forM_ exprs $ \expr -> do
    --lift $ print expr
    --lift $ putStrLn (prettyPrint expr)
    eval expr env
  pure env


replGetInput cont = do
  case cont of
    Just _ -> putStr "... "
    Nothing -> putStr "> "
  flush
  input_ <- catchJust (guard . isEOFError) (fmap Just getLine) (const $ pure Nothing)
  input <- case input_ of
    Nothing -> exitSuccess --TODO: replace this with "replGetInput cont"
    Just input -> pure input
  if null input then exitSuccess else do
  let
    input' = case cont of
      Just cont -> cont ++ "\n" ++ input
      Nothing -> input
  if countBrackets input' > 0 then replGetInput (Just input') else pure input'

countBrackets [] = 0
countBrackets (x:xs)
  | x `elem` "([{" = countBrackets xs + 1
  | x `elem` ")]}" = countBrackets xs - 1
  | True = countBrackets xs
