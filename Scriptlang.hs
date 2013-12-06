{-# LANGUAGE TupleSections #-}

module Scriptlang where

{- TODO
  To get working:
    map f xs -> if (xs.empty) [] else f (xs.head) : map f xs.tail
      (need parens around a lot of stuff)
    map (a => a + 2) [1,2,3]
    a => a + 2
  To implement:
    Providing only part of a function's argument at a time, and substituting the rest later
    Function overloading
    Types and pattern matching
    Generators
    Syntax for specifying chars with a hex code
    Line numbers for errors

  Improve syntax errors:
    When typing "5 /*" it should say it expects the end of the comment
    When typing "5 /" it should say it expects the other "/" to complete the single-line comment
  When you define a function with 2 arguments of the same name, it should say so instead of giving the message "Can't reassign identifier". That message should never appear, ever.
  TODO: do by-name optional parameters make sense?
  TODO: entering multiline expressions on the REPL
  Verify that pipes work and are actually useful
  Add glob and regex support
    Glob syntax:
      * - match 0 or more unknown chars
      \ - escape char - next char is treated as a normal char
      We could add more glob syntax than this, but it's probably better to use a regex for anything more complicated
  Avoid using "system"; always use "rawSystem"
  TODO: disallow ~ on everything but parameters - zero-argument functions have replaced them
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
  env' <- runErrorT $ runFile "stdlib" env
  case env' of
    Left err -> putStrLn err
    Right env -> repl env

repl env = do
  input <- replGetInput Nothing
  expr_ <- runErrorT (parseInput "" input parseStatement)
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
    --lift $ print expr
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
    Nothing -> exitSuccess
    Just input -> pure input
  if null input then exitSuccess else do
  let
    input' = case cont of
      Just cont -> cont ++ " " ++ input
      Nothing -> input
  --if countBrackets input' > 0 then replGetInput (Just input') else pure input'
  pure input'

