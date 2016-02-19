module Test where

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
import Test.HUnit

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import Util

import Expr
import Parse
import Eval
import Repl


testEnv :: IO (Either String EnvStack)
testEnv = do
  stdlibFile <- stdlibFilename
  env <- startEnv
  runErrorT $ envNewScope =<< runFile stdlibFile env

{-# NOINLINE testEnv_ #-}
testEnv_ :: IORef (Either String EnvStack)
testEnv_ = unsafePerformIO (newIORef =<< testEnv)

getTestEnv = get testEnv_

isLeft (Left _) = True
isLeft (Right _) = False
isRight (Left _) = False
isRight (Right _) = True
fromLeft (Left x) = x
fromRight (Right x) = x

testRun :: EnvStack -> String -> IO (Either String Expr)
testRun env str = do
  stdlibFile <- stdlibFilename
  runErrorT $ fst <$> parseEval str env

testRun' str = do
  env <- fromRight <$> getTestEnv
  (prettyPrint <$>) <$> testRun env str

testEqual :: String -> String -> Assertion -- IO Bool
testEqual a b = do
  env <- getTestEnv
  when (isLeft env) $ assertFailure "Failed to eval env"
  env <- pure (fromRight env)
  exprA <- testRun env a
  exprB <- testRun env b
  case (exprA, exprB) of
    (Right exprA, Right exprB) -> do
      eq <- exprEq exprA exprB
      assertBool ("Expected " ++ a ++ " to eval to " ++ b ++ " but got " ++ prettyPrint exprA) eq
    (Right _, Left errB) -> assertFailure $ "Failed to eval `" ++ b ++ "`; got error " ++ errB
    (Left errA, Right _) -> assertFailure $ "Failed to eval `" ++ a ++ "`; got error " ++ errA
    (Left errA, Left errB) -> assertFailure $ "Failed to eval `" ++ a ++ "` and `" ++ b ++ "`; got errors " ++ errA ++ " and " ++ errB

testEq = TestCase ... testEqual
testEq' name = (TestLabel name . TestCase) ... testEqual

arithTests = TestLabel "arith" $ TestList [
  testEq "2+3" "5",
  testEq "2*3" "6",
  testEq "5-4" "1",
  testEq "1/2" "0.5",
  testEq "2 + 3 * 4" "14",
  testEq "2+3 * 4" "20"
  ]

varTests = TestLabel "var" $ TestList [
  testEq "(a = 5; a <- a*2; a)" "10",
  testEq "(a = 5; (a = 10); a)" "5",
  testEq "(a = 5; (a <- 10); a)" "10"
  ]

fnTests = TestLabel "fn" $ TestList [
  testEq "(sumUpTo = n -> (n * (n+1)) div 2; sumUpTo 100)" "5050",
  testEq "(fac = n -> if (n==0) 1 else n * fac (n-1); fac 5)" "120"
  ]

objTests = TestLabel "obj" $ TestList [
  testEq "(x = {a=5}; x.a)" "5",
  testEq "(x = {a=5}; x.a <- 10; x.a)" "10",
  testEq "(x = {a=5}; y = new x {b=4}; y.a <- 10; x.a)" "5"
  ]

allTests = TestList [arithTests, varTests, fnTests, objTests]

runTests = getTestEnv >> runTestTT allTests


testParse parser = forever $ do
  input <- replGetInput Nothing
  lift $ case parse (parser <* eof) "test" input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right expr -> print expr

