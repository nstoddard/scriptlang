{-# LANGUAGE TupleSections #-}

module Scriptlang where

{- TODO
  To implement:
    Map, filter, etc should be methods on lists, not functions
    Providing only some of a function's arguments at a time, and substituting the rest later
    Function overloading
    Types and pattern matching
    Generators
    Syntax for specifying chars with a hex code
    Line numbers for errors
    I/O
      Should it be "5 println" or "println 5"?
        It should probably be "println 5", because it shouldn't be possible for objects to override println. However, they should be able to override toString, but toString should be implemented by default in all objects and should just print "<object>" or something. We certainly need a way to create default environments for objects - they shouldn't begin with an empty environment.
      toString
    Extension methods
    Finish matchParams
    Add a method to be called when a method isn't defined
    Data declarations
    Maps - perhaps I should hold off on implementing this until I've implemented pattern matching - it seems that pattern matching and maps could be combined to simplify the language - this is one thing that I find irritating about Scala; it's sometimes hard to decide which one to use
    Glob syntax and regexes
    Command history
    Function composition (f.o g, perhaps); treating functions as objects
    Calling an object as though it's a function?
    Cloning?
    Unit testing
    Interfacing between scripts - this should be fairly easy
    Reflection - checking which fields, methods, etc an object supportss
    Imports
    Treat functions as objects with an "apply" method and "o" as a composition operator
    Currying, sections, tuple sections, list sections

  Improve syntax errors
  Do by-name optional parameters make sense?
  Disallow ~ on everything but parameters - zero-argument functions have replaced them
  Consider adding by-reference parameters - when passing a variable to it, instead of passing its value it would pass the variable itself
  Should it be possible to overload assignment?
  Add fields - like Scala's getters and setters
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

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import Util

import Expr
import Parse
import Eval

main = do
  env <- startEnv
  env <- runErrorT $ runFile "stdlib" env
  case env of
    Left err -> putStrLn err
    Right env -> repl env



repl env = do
  input <- replGetInput Nothing
  expr_ <- runErrorT (parseInput "" input parseExpr)
  case expr_ of
    Left err -> putStrLn err >> repl env
    Right expr -> do
      print expr
      putStrLn (prettyPrint expr)

      res <- runErrorT (replEval expr env)
      case res of
        Left err -> putStrLn err >> repl env
        Right (EVoid, env') -> repl env'
        Right (expr', env') -> do
          putStrLn (prettyPrint expr')
          repl env'

parseInput :: String -> String -> Parsec String () a -> IOThrowsError a
parseInput srcName input parser = case parse (parseWholeInput parser) srcName input of
  Left err -> throwError ("Syntax error " ++ show err)
  Right expr -> pure expr

runFile :: String -> EnvStack -> IOThrowsError EnvStack
runFile filename env = do
  exists <- lift $ doesFileExist filename
  if not exists then throwError ("File doesn't exist: " ++ filename) else do
  input <- lift $ Strict.readFile filename
  exprs <- parseInput filename input parseCompound
  lift $ putStrLn $ "Running file: " ++ filename
  forM_ exprs $ \expr -> do
    lift $ print expr
    lift $ putStrLn (prettyPrint expr)
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
