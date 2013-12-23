{-# LANGUAGE TupleSections #-}

module Scriptlang where

--RESUME: I was just about to start making spaces matter in operators: "1+2 * 3+4" should be different than "1 + 2*3 + 4", and "f -a" should pass "a" as a flag to "f"

{- TODO
  For current version:
    Map, filter, etc should be methods on lists, not functions

  Not working:
    (_) 5
      (_) should be the identity functoin

  Running other programs:
    ls `a
    ls 'a
    ls -a
    ls \a
  Use 3rd one; this can be made syntactically unambiguous with these rules:
    a + b - applying the "+" operator to a with b as the argument
    a+b - same thing
    a +b - calling the function a with "+b" as an argument
    a+ b - invalid
  Note that with this syntax, "f -5" doesn't call f with -5 as the argument, it calls f with a flag of "5" as the argument. You'd have to write "f (-5)".
  1+2 * 3+4 != 1 + 2*3 + 4

  In later versions:
    More I/O
    Glob syntax and regexes
    Command history
    I/O redirection and pipes for external programs
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
      They should also have a "+" operator for adding 2 functions together, and so on - perhaps these operators can be automatically generated for every possible operator
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
  ("help", makeString "TODO: write documentation"),
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
    expr <- call obj "toString" [] env
    case expr of
      EObj (PrimObj (PString str) _) -> lift $ putStr str
      x -> throwError $ "toString must return a string; not " ++ prettyPrint x
    pure EVoid),
  ("println", objUnop' $ \obj env -> do
    expr <- call obj "toString" [] env
    case expr of
      EObj (PrimObj (PString str) _) -> lift $ putStrLn str
      x -> throwError $ "toString must return a string; not " ++ prettyPrint x
    pure EVoid),
  ("readln", nilop $ makeString <$> lift getLine),
  ("eval", objUnop' $ \obj env -> case obj of
    PrimObj (PString str) _ -> fst <$> parseEval str env
    x -> throwError $ "Can't evaluate non-string: " ++ prettyPrint x),
  ("cd", stringUnop $ \str -> do
    lift $ setCurrentDirectory str
    makeString <$> lift getCurrentDirectory),
  ("wd", nilop $ makeString <$> lift getCurrentDirectory)
  ]

parseEval str env = do
  expr <- parseInput "" str parseExpr desugar
  eval expr env

debugging env = do
  debug <- lookupID "debug" env
  case debug of
    EObj (PrimObj (PBool True) _) -> pure True
    EObj (PrimObj (PBool False) _) -> pure False
    x -> throwError $ "Invalid value for debug: " ++ prettyPrint x

main = do
  putStrLn "Scriptlang version 0.1"
  env <- startEnv
  env <- runErrorT $ envNewScope =<< runFile "stdlib" env
  case env of
    Left err -> putStrLn err
    Right env -> repl env

repl env = do
  input <- replGetInput Nothing
  expr_ <- runErrorT (parseInput "" input parseExpr desugar)
  case expr_ of
    Left err -> putStrLn err >> repl env
    Right expr -> do
      debug <- runErrorT (debugging env)
      case debug of
        Left err -> putStrLn err >> repl env
        Right debug -> when debug $ do
          print expr
          putStrLn (prettyPrint expr)

      res <- runErrorT (replEval expr env)
      case res of
        Left err -> putStrLn err >> repl env
        Right (EVoid, env') -> repl env'
        Right (expr', env') -> do
          case expr' of
            EObj (PrimObj (PString str) _) -> putStrLn str
            _ -> putStrLn (prettyPrint expr')
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
    Nothing -> exitSuccess
    Just input -> pure input
  if null input then replGetInput cont else do
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
