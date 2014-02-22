{-# LANGUAGE TupleSections #-}

module Main where

{- TODO
  The code for detecting imbalanced groupers doesn't ignore groupers in comments

  In later versions:
    "Invalid argument to <implementation detail>" should be changed to something more meaningful
    Add a way to look up the definition of a function
    Allow user-defined operator precedence and associativity. the current rule just doesn't work very well and is too inflexible. However, each operator must always have the same precedence and associativity no matter what object it's called on, otherwise it would be unparseable.
    Don't print floating-point numbers in scientific notation so often; certainly don't for numbers like "0.01"
    Always print the path with forward slashes rather than backslashes (since backslashes are for escape characters, you'd need to write "\\" when you could just write "/") - this may require reimplementing things like "pwd" in order to get the slashes right.
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
    Reflection - checking which fields, methods, etc an object supports
    Imports
    Consider adding by-reference parameters - when passing a variable to it, instead of passing its value it would pass the variable itself
    Should it be possible to overload assignment?
    Add fields - like Scala's getters and setters?
      They should behave sort of like variables.
    Functions could have a "+" operator for adding 2 functions together, and so on - perhaps these operators can be automatically generated for every possible operator
    Make sure _ and especially _* work properly with by-name parameters.
    Function overloading
    Line numbers for errors
    Add a method to be called when a method isn't defined
    Cloning of objects?

  Do by-name optional parameters make sense?
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
  ("execRaw", ePrim [reqParam "proc"] $ \env -> do
    proc <- envLookup' "proc" env
    case proc of
      (EObj (PrimObj (PString proc) _)) -> do
        lift $ system proc
        pure (EVoid, env)
      _ -> throwError "Invalid argument to execRaw"),
  ("env", nilop' $ \env -> lift (print =<< getEnv env) *> pure (EVoid,env)), --TODO: THIS DOESN'T WORK
  ("envOf", unop $ \expr -> (lift . (print <=< getEnv) =<< getExprEnv expr) *> pure EVoid),
  ("print", objUnop' $ \obj env -> do
    expr <- call obj "toString" [] env
    case expr of
      EObj (PrimObj (PString str) _) -> lift $ putStr str
      x -> throwError $ "toString must return a string; not " ++ prettyPrint x
    pure (EVoid,env)),
  ("println", objUnop' $ \obj env -> do
    expr <- call obj "toString" [] env
    case expr of
      EObj (PrimObj (PString str) _) -> lift $ putStrLn str
      x -> throwError $ "toString must return a string; not " ++ prettyPrint x
    pure (EVoid,env)),
  ("readln", nilop $ makeString <$> lift getLine),
  ("eval", objUnop' $ \obj env -> case obj of
    PrimObj (PString str) _ -> (,env) <$> fst <$> parseEval str env
    x -> throwError $ "Can't evaluate non-string: " ++ prettyPrint x),
  ("cd", stringUnop $ \str -> do
    lift $ setCurrentDirectory str
    makeString <$> lift getCurrentDirectory),
  ("wd", nilop $ makeString . replace '\\' '/' <$> lift getCurrentDirectory),
  ("run", stringUnop' $ \file env -> do
    (EVoid,) <$> runFile file env)
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

stdlib = "\
  \var debug <- false\n\
  \\n\
  \pi = 3.141592653589793238462643383279\n\
  \tau = 2*pi\n\
  \\n\
  \sumUpTo n -> (n * (n+1)) div 2\n\
  \fac n -> if (n==0) 1 else n * fac (n-1)\n\
  \\n\
  \clear -> execRaw 'clear'\n\
  \\n\
  \id x -> x\n\
  \\n\
  \list xs* -> xs\n\
  \\n\
  \while ~cond ~f -> if cond {f; while ~cond ~f}\n\
  \\n\
  \compose a b -> x => a (b (x))\n\
  \println 'Scriptlang version 0.1'\n\
  \pwd -> println (wd)\n\
  \pwd\n\
  \"

main = do
  env <- startEnv
  env <- runErrorT $ envNewScope =<< runString stdlib env -- =<< runFile "stdlib" env
  case env of
    Left err -> putStrLn err
    Right env -> repl env

testParse parser = forever $ do
  input <- replGetInput Nothing
  case parse (parser <* eof) "test" input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right expr -> print expr

repl env = do
  input <- replGetInput Nothing
  expr_ <- runErrorT (parseInput "" input parseExpr desugar)
  case expr_ of
    Left err -> putStrLn err >> repl env
    Right expr -> do
      {-debug <- runErrorT (debugging env)
      case debug of
        Left err -> putStrLn err >> repl env
        Right debug -> when debug $ do
          print expr
          putStrLn (prettyPrint expr)-}

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

runString :: String -> EnvStack -> IOThrowsError EnvStack
runString input env = do
  exprs <- parseInput "" input parseCompound (map desugar)
  forM_ exprs $ \expr -> do
    --lift $ print expr
    --lift $ putStrLn (prettyPrint expr)
    eval expr env
  pure env


replGetInput cont = do
  case cont of
    Just _ -> putStr "... "
    Nothing -> putStr "script> "
  flush
  input_ <- catchJust (guard . isEOFError) (fmap Just getLine) (const $ pure Nothing)
  input <- case input_ of
    Nothing -> exitSuccess
    Just input -> pure input
  if null input then exitSuccess {-replGetInput cont-} else do
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
