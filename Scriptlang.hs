{-# LANGUAGE TupleSections #-}

module Main where

{- TODO
  TODO for first version:
    Always use system instead of rawSystem - rawSystem doesn't handle things like sbt correctly; system is harder to use correctly, but gives better results
      This could mean that I don't need to use slash commands anymore.

    Add raw strings. Sometimes I need to paste in paths that include backslashes, and I don't want to have to escape them all. They would also be helpful for regexes.
    The code for detecting imbalanced groupers doesn't ignore groupers in comments
    Sometimes parse errors give a line way before the actual error, probably caused by excessive "try" statements

    Generators
      The syntax should look something like this:
        read "in.txt" | words | sort | unwords | write "out.txt"
      Perhaps they should be a bit more compact:
        ?"in.txt" | words | sort | unwords | !"out.txt"
      With "?" meaning input, and "!" meaning output.
      I need to fix my types first. I have too many lists and they all have to implement most operators separately.
        I need at least List and Stream. I might be able to incorporate the string functions into them; I don't want to also have String and CharStream. If it were a more strongly typed language I'd have Stream<Char> and so on. If I include string functions in lists, it just means that they'll fail when applied to a non-string.
    Imports
    Glob syntax and regexes
    Extension methods
    Function overloading
    "Invalid argument to <implementation detail>" should be changed to something more meaningful
    Allow user-defined operator precedence and associativity. the current rule just doesn't work very well and is too inflexible. However, each operator must always have the same precedence and associativity no matter what object it's called on, otherwise it would be unparseable.
    Don't print floating-point numbers in scientific notation so often; certainly don't for numbers like "0.01"
    I/O redirection and pipes for external programs
    Syntax for specifying chars with a hex code
    Maps
    Make sure _ and especially _* work properly with by-name parameters.
    Add a method to be called when a method isn't defined

  TODO for later versions:
    Add a way to look up the definition of a function
    Command history
    Types and pattern matching
    Data declarations
    Reflection - checking which fields, methods, etc an object supports
    Consider adding by-reference parameters - when passing a variable to it, instead of passing its value it would pass the variable itself
    Should it be possible to overload assignment?
    Add fields - like Scala's getters and setters?
      They should behave sort of like variables.
    Line numbers for errors

  Do by-name optional parameters make sense?

  Notes:
    I would've liked to add operators like "+" to add 2 functions together, but that wouldn't work with the current language design and would require major changes, if it could be done at all.
-}

import Prelude hiding (catch)
import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Error
import Data.Maybe
import Data.Char
import System.IO.Unsafe
import System.IO.Error hiding (try, catch)
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
import qualified System.FilePath as P

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import System.Console.Haskeline as H

import Util

import Expr
import Parse
import Eval



--Change this to false before release
debug = True

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
    exists <- lift $ doesDirectoryExist str
    if exists then do
      lift $ setCurrentDirectory str
      makeString <$> lift workingDirectory
    else throwError $ "Directory doesn't exist: " ++ str),
  ("wd", nilop $ makeString <$> lift workingDirectory),
  ("run", stringUnop' $ \file env -> do
    (EVoid,) <$> runFile file env)
  ]

workingDirectory = replace '\\' '/' <$> getCurrentDirectory

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
  --install_interrupt_handler (pure ())
  env <- startEnv
  stdlibFile <- if debug then pure "stdlib.script"
    else (P.</>"stdlib.script") <$> getAppUserDataDirectory "scriptlang"
  env <- runErrorT $ envNewScope =<< runFile stdlibFile env
  case env of
    Left err -> putStrLn err
    Right env -> runInputT defaultSettings $ repl env

testParse parser = forever $ do
  input <- replGetInput Nothing
  lift $ case parse (parser <* eof) "test" input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right expr -> print expr

repl env = do
  input <- replGetInput Nothing{-catch (replGetInput Nothing) $ \exception -> case exception of
    UserInterrupt -> putStrLn "^c\n" >> pure "{}"
    e -> error $ "Unhandled exception: " ++ show e-}

  expr_ <- lift $ runErrorT (parseInput "" input parseExpr desugar)
  case expr_ of
    Left err -> lift (putStrLn err) >> repl env
    Right expr -> do
      debug <- lift $ runErrorT (debugging env)
      case debug of
        Left err -> lift (putStrLn err) >> repl env
        Right debug -> when debug $ lift $ do
          print expr
          putStrLn (prettyPrint expr)

      res <- lift $ runErrorT (replEval expr env)
      case res of
        Left err -> lift (putStrLn err) >> repl env
        Right (EVoid, env') -> repl env'
        Right (expr', env') -> do
          case expr' of
            EObj (PrimObj (PString str) _) -> lift $ putStrLn str
            _ -> lift $ putStrLn (prettyPrint expr')
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

ctrlC :: MonadException m => SomeException -> InputT m (Maybe String)
ctrlC e = pure (Just "{}")

replGetInput cont = do
  let prompt = if isJust cont then "... " else "script> "
  input_ <- H.catch (getInputLine prompt) $ ctrlC
  input <- case input_ of
    Nothing -> lift exitSuccess
    Just input -> pure input
  if null input then if debug then lift exitSuccess else replGetInput cont else do
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
