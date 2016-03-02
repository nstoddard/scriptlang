{-# LANGUAGE TupleSections #-}

module Repl where

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
import qualified System.Environment as E
import System.Directory
import qualified System.IO.Strict as Strict
import Data.Foldable (asum, toList)
import Debug.Trace
import System.Process
import qualified System.FilePath as P
import System.IO
import Test.HUnit

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import System.Console.Haskeline as H
import Control.Concurrent hiding (writeChan)
import Control.Concurrent.BoundedChan

import Util hiding (writeChan)

import Expr
import Parse
import Eval


-- TODO: does Cabal have a way to avoid this?
release = False
--If true, print debug info about expressions
debug = False

{-debugging env = do
  debug <- lookupID "debug" env
  case debug of
    EObj (PrimObj (PBool True) _) -> pure True
    EObj (PrimObj (PBool False) _) -> pure False
    x -> throwError $ "Invalid value for debug: " ++ prettyPrint x-}


parseEval str env = do
  expr <- parseInput "" str parseExpr desugar
  eval expr env

parseInput :: String -> String -> Parsec String () a -> (a->a) -> IOThrowsError a
parseInput srcName input parser desugar = case parse (parseWholeInput parser) srcName input of
  Left err -> throwError ("Syntax error " ++ show err)
  Right expr -> pure $ desugar expr

stdlibFilename = dataFile "stdlib.script"
historyFilename = dataFile "history"

dataFile filename = if not release then pure filename
  else (P.</> filename) <$> getAppUserDataDirectory "scriptlang"


debugPrint expr = when debug $ lift $ do
  print expr
  putStrLn (prettyPrint expr)
  putStrLn ""

repl env = do
  input <- replGetInput Nothing
  expr_ <- lift $ runErrorT (parseInput "" input parseExpr desugar)
  case expr_ of
    Left err -> lift (putStrLn err) >> repl env
    Right expr -> do
      {-debug <- lift $ runErrorT (debugging env)
      case debug of
        Left err -> lift (putStrLn err) >> repl env
        Right debug -> when debug $ lift $ do
          print expr
          putStrLn (prettyPrint expr)-}
      debugPrint expr

      res <- handleCtrlC (Left "Interrupted") $ lift $ runErrorT (replEval expr env)
      case res of
        Left err -> lift (putStrLn err) >> repl env
        Right (EVoid, env') -> repl env'
        Right (expr', env') -> do
          case getString' expr' of
            Just str -> lift $ putStrLn str
            Nothing -> lift $ putStrLn (prettyPrint expr')
          repl env'


-- TODO: this doesn't update the environment!
runFile :: String -> EnvStack -> IOThrowsError EnvStack
runFile filename env = do
  exists <- lift $ doesFileExist filename
  if not exists then throwError ("File doesn't exist: " ++ filename) else do
  input <- lift $ Strict.readFile filename
  exprs <- parseInput filename input parseCompound (map desugar)
  when debug $ lift $ putStrLn $ "Running file: " ++ filename
  forM_ exprs $ \expr -> do
    debugPrint expr
    eval expr env
  pure env

runString :: String -> EnvStack -> IOThrowsError EnvStack
runString input env = do
  exprs <- parseInput "" input parseCompound (map desugar)
  forM_ exprs $ \expr -> do
    debugPrint expr
    eval expr env
  pure env


handleCtrlC = H.handle . ctrlC where
  ctrlC :: a -> AsyncException -> InputT IO a
  ctrlC def UserInterrupt = pure def
  ctrlC def e = lift (putStrLn $ "Unknown exception: " ++ show e) >> pure def

replGetInput cont = do
  let prompt = if isJust cont then "... " else "script> "
  input_ <- handleCtrlC (Just "void") $ getInputLine prompt
  input <- case input_ of
    Nothing -> lift exitSuccess
    Just input -> pure input
  if null input then if not release then lift exitSuccess else replGetInput cont else do
  let
    input' = case cont of
      Just cont -> cont ++ "\n" ++ input
      Nothing -> input
  if countBrackets input' > 0 then replGetInput (Just input') else pure input'

countBrackets [] = 0
countBrackets (x:xs)
  | x `elem` "([{" = countBrackets xs + 1
  | x `elem` ")]}" = countBrackets xs - 1
  | otherwise = countBrackets xs



startEnv :: IO EnvStack
startEnv = envStackFromList [
  ("-", primUnop $ onNum negate),
  ("!", primUnop $ onBool not),
  ("exit", nilop (lift exitSuccess)),
  ("help", makeString "TODO: write documentation"),
  ("execRaw", ePrim [reqParam "proc"] $ \env -> do
    proc <- envLookup' "proc" env
    case getString' proc of
      Just proc -> do
        lift $ system proc
        pure (EVoid, env)
      Nothing -> throwError "Invalid argument to execRaw"),
  ("env", nilop' $ \env -> lift (print =<< getEnvs env) *> pure (EVoid,env)), --TODO: THIS DOESN'T WORK
  ("envOf", unop $ \expr -> (lift . (print <=< getEnvs) =<< getExprEnv expr) *> pure EVoid),
  ("print", objUnop' $ \obj env -> do
    expr <- call obj "toString" [] env
    case getString' expr of
      Just str -> lift $ putStr str
      Nothing -> throwError $ "toString must return a string; not " ++ prettyPrint expr
    pure (EVoid,env)),
  ("println", objUnop' $ \obj env -> do
    expr <- call obj "toString" [] env
    case getString' expr of
      Just str -> lift $ putStrLn str
      Nothing -> throwError $ "toString must return a string; not " ++ prettyPrint expr
    pure (EVoid,env)),
  ("readln", nilop $ makeString <$> lift getLine),
  ("eval", objUnop' $ \obj env -> case getString2' obj of
    Just str -> (,env) . fst <$> parseEval str env
    Nothing -> throwError $ "Can't evaluate non-string: " ++ prettyPrint obj),
  ("cd", stringUnop $ \str -> do
    exists <- lift $ doesDirectoryExist str
    if exists then do
      lift $ setCurrentDirectory str
      makeString <$> lift workingDirectory
    else throwError $ "Directory doesn't exist: " ++ str),
  ("wd", nilop $ makeString <$> lift workingDirectory),
  ("run", stringUnop' $ \file env -> (EVoid,) <$> runFile file env),
  ("withGen", unop' $ \arg env -> case arg of
    EObj (FnObj {}) -> do
      gen@(EObj (PrimObj (PGen ioRef chan) _)) <- makeGen 10
      lift $ forkIO $ do
        let
          yield = unop $ \x -> do
            lift $ writeChan chan (Just x)
            pure EVoid
        res <- runErrorT $ do
          apply arg [Arg yield] env
          lift $ writeChan chan Nothing
        case res of
          Left err -> putStrLn $ "Error in generator: " ++ err
          Right val -> pure ()
      pure (gen,env)
    _ -> throwError $ "Invalid argument to withGen: " ++ prettyPrint arg),
  ("withFile", triop' (\path mode fn env -> case getString' path of
    Just path -> case getString' mode of
      Just mode -> case fn of
        EObj (FnObj {}) -> do
          let mode' = getMode mode
          handle <- lift $ openFile path mode'
          lift $ print =<< hGetBuffering handle
          apply fn [Arg $ makeHandle handle path] env
          lift $ hClose handle
          pure (EVoid, env)
        _ -> throwError "Invalid function in withFile"
      Nothing -> throwError "Invalid mode in withFile"
    Nothing -> throwError "Invalid path in withFile"))
  ]

getMode "r" = ReadMode
getMode "w" = WriteMode
getMode "a" = AppendMode
getMode "rw" = ReadWriteMode

workingDirectory = replace '\\' '/' <$> getCurrentDirectory
