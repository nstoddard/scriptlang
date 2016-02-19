{-# LANGUAGE TupleSections #-}

module Main where

{- TODO
  TODO for first version:
    Files aren't closed at the end of withFile if interrupted by ctrl-c
    After compiling the interpreter and running it at command line startup, it doesn't handle ctrl-c correctly - it interrupts processes fine, but when you press ctrl-c it should print "^c" and go to the next line. It prints a newline but it doesn't show up until you type something else. If you press ctrl-c twice in a row, it quits.
    Copying a file with 'read "Scriptlang.hs" | write "copy"' is really slow, only a few KB/sec
      The current pipe mechanism isn't well-suited to very long strings of chars - it's good for sequences with only a few hundred elements, maybe a few thousand
      What should replace it - perhaps batch reads/writes?
    When you create a generator function with a typo:
      fileGen file -> makeGen (yield => withFile file "r" (file => while (!(file.atEOF)) {yield (file.readChar)}))
    And try to use it:
      testGen = fileGen "test"
    It gives a nonsensical error message; it should tell you that makeGen is not found
    withGen should take an optional first parameter of how big its buffer should be
    There needs to be a way to terminate a generator early
    By-name values act similar to variables

    Why did I use {} rather than () for the generator examples below?
    Catch divide-by-zero errors, and every other error, and don't terminate the app
    Why doesn't this:
      a b.c
    Parse the same as:
      a (b.c)
    Sometimes the second one works but the first doesn't (but sometimes they both work)
    It seems that this doesn't work for simpleGen.cur because that's a zero-argument function. The way to resolve this might be to make it into a new type of value, which is evaluated sooner than a zero-argument function but that isn't constant.
    Would by-name values fix this problem? I already have them implemented and they might have the required semantics. I've been trying to avoid them, though; they're a bit confusing so they should be avoided whenever possible. But they might work for this case.
    Another case for them is in "wd", which would let me replace "println (wd)" with "println wd"
    I'll avoid fixing this for now; I need to simplify the evaluator first. Otherwise it'll get way too big to manage.

    Allow interrupting generators
    Add raw strings. Sometimes I need to paste in paths that include backslashes, and I don't want to have to escape them all. They would also be helpful for regexes.
    The code for detecting imbalanced groupers doesn't ignore groupers in comments
    Sometimes parse errors give a line way before the actual error, probably caused by excessive "try" statements

    Add syntax like "3 `div` 2" to replace the stupid syntax "3 div 2". Then we can do things like "6 `div` 2 `div` 3" where before we had to do "6 div 2 | div 3" which is really dumb. This also lets us use pipes exclusively for chaining together generators and consumers. Unfortunately, backquoted identifiers currently allow you to include arbitrary characters in identifiers, and even use keywords as identifiers. That's a stupid idea that I got from Scala. I should get rid of it. Nobody would ever use it. I hope not, anyway. It's in Scala because it needs to interop with Java, and Scala has some keywords that Java doesn't have. If in Java, you have a variable named "val", to access it from Scala you need backquotes around it. I don't have that problem here.
    Generators
      The syntax should look something like this:
        read "in.txt" | words | sort | unwords | write "out.txt"
      Perhaps they should be a bit more compact:
        ?"in.txt" | words | sort | unwords | !"out.txt"
      With "?" meaning input, and "!" meaning output.
      read filename -> withGen {yield => withFile filename {file =>
        while (!file.atEnd)
          yield file.readChar
      }}
      write filename gen -> withFile filename {file =>
        while (gen.moveNext)
          file.writeChar gen.cur
      }
      dupEvery gen -> withGen {yield =>
        while (gen.moveNext) {
          yield gen.cur
          yield gen.cur
        }
      }
      read "in" | dupEvery | write "out" = write "out" (dupEvery (read "in"))
    Imports
    Glob syntax and regexes
    Extension methods
    Function overloading
      Need overloading by # of arguments but not necessarily by type
    "Invalid argument to <implementation detail>" should be changed to something more meaningful
    Allow user-defined operator precedence and associativity. the current rule just doesn't work very well and is too inflexible. However, each operator must always have the same precedence and associativity no matter what object it's called on, otherwise it would be unparseable.
    Don't print floating-point numbers in scientific notation so often; certainly don't for numbers like "0.01"
    I/O redirection and pipes for external programs
    Syntax for specifying chars with a hex code
    Maps
    Add a method to be called when a method isn't defined

  TODO for later versions:
    Make sure _ and especially _* work properly with by-name parameters.
    Add a way to look up the definition of a function
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
import qualified System.Environment as E
import System.Directory
import qualified System.IO.Strict as Strict
import Data.Foldable (asum, toList)
import Debug.Trace
import System.Process
import qualified System.FilePath as P
import System.IO

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import System.Console.Haskeline as H
import Control.Concurrent hiding (writeChan)
import Control.Concurrent.BoundedChan

import Util

import Expr
import Parse
import Eval



-- TODO: does Cabal have a way to avoid this?
release = False
--If true, print debug info about expressions
debug = True

startEnv :: IO EnvStack
startEnv = envStackFromList [
  ("-", primUnop $ onNum negate negate),
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
  ("env", nilop' $ \env -> lift (print =<< getEnv env) *> pure (EVoid,env)), --TODO: THIS DOESN'T WORK
  ("envOf", unop $ \expr -> (lift . (print <=< getEnv) =<< getExprEnv expr) *> pure EVoid),
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
    Just str -> (,env) <$> fst <$> parseEval str env
    Nothing -> throwError $ "Can't evaluate non-string: " ++ prettyPrint obj),
  ("cd", stringUnop $ \str -> do
    exists <- lift $ doesDirectoryExist str
    if exists then do
      lift $ setCurrentDirectory str
      makeString <$> lift workingDirectory
    else throwError $ "Directory doesn't exist: " ++ str),
  ("wd", nilop $ makeString <$> lift workingDirectory),
  ("run", stringUnop' $ \file env -> do
    (EVoid,) <$> runFile file env),
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
  ("withFile", triop' (\path mode fn env -> do
    case getString' path of
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

parseEval str env = do
  expr <- parseInput "" str parseExpr desugar
  eval expr env

{-debugging env = do
  debug <- lookupID "debug" env
  case debug of
    EObj (PrimObj (PBool True) _) -> pure True
    EObj (PrimObj (PBool False) _) -> pure False
    x -> throwError $ "Invalid value for debug: " ++ prettyPrint x-}


dataFile filename = if not release then pure filename
  else (P.</> filename) <$> getAppUserDataDirectory "scriptlang"

stdlibFilename = dataFile "stdlib.script"
historyFilename = dataFile "history"

main = do
  env <- startEnv
  stdlibFile <- stdlibFilename
  env <- runErrorT $ envNewScope =<< runFile stdlibFile env

  args <- E.getArgs
  if null args then do
    historyFile <- historyFilename
    case env of
      Left err -> putStrLn err
      Right env -> runInputT (Settings noCompletion (Just historyFile) True) $ repl env
  else do
    case env of
      Left err -> putStrLn err
      Right env -> do
        envRef <- newIORef env
        forM_ args $ \arg -> do
          env <- runErrorT $ runFile arg =<< lift (get envRef)
          case env of
            Left err -> putStrLn err >> exitFailure
            Right env -> envRef $= env



testParse parser = forever $ do
  input <- replGetInput Nothing
  lift $ case parse (parser <* eof) "test" input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right expr -> print expr

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
      when debug $ lift $ do
        print expr
        putStrLn (prettyPrint expr)
        putStrLn ""

      res <- handleCtrlC (Left "Interrupted") $ lift $ runErrorT (replEval expr env)
      case res of
        Left err -> lift (putStrLn err) >> repl env
        Right (EVoid, env') -> repl env'
        Right (expr', env') -> do
          case getString' expr' of
            Just str -> lift $ putStrLn str
            Nothing -> lift $ putStrLn (prettyPrint expr')
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
  when debug $ lift $ putStrLn $ "Running file: " ++ filename
  forM_ exprs $ \expr -> do
    when debug $ lift $ do
        print expr
        putStrLn (prettyPrint expr)
        putStrLn ""
    eval expr env
  pure env

runString :: String -> EnvStack -> IOThrowsError EnvStack
runString input env = do
  exprs <- parseInput "" input parseCompound (map desugar)
  forM_ exprs $ \expr -> do
    when debug $ lift $ do
        print expr
        putStrLn (prettyPrint expr)
        putStrLn ""
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
  | True = countBrackets xs
