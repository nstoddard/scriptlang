module Test where

import Prelude
import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Error
import Data.Maybe
import Data.Char
import System.IO.Unsafe
import System.IO.Error
import Control.Exception hiding (try)
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
fromLeft (Right _) = undefined
fromRight (Right x) = x
fromRight (Left _) = undefined

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
      eq <- runErrorT $ exprEq exprA exprB
      case eq of
        Left err -> assertFailure $ "Failed to compare for equality: `" ++ a ++ "` and `" ++ b ++ "`; got error " ++ err
        Right eq -> assertBool ("Expected " ++ a ++ " to eval to " ++ prettyPrint exprB ++ " but got " ++ prettyPrint exprA) eq
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
  testEq "2+3 * 4" "20",
  testEq "3^3^3" "3^(3^3)",
  testEq "2*3+4 * 10" "100"
  ]

varTests = TestLabel "var" $ TestList [
  testEq "(a = 5; a <- a*2; a)" "10",
  testEq "(a = 5; (a = 10); a)" "5",
  testEq "(a = 5; (a <- 10); a)" "10"
  ]

fnTests = TestLabel "fn" $ TestList [
  testEq "(x -> x) 5" "5",
  testEq "(xs* -> xs) 1 2 3" "[1,2,3]",
  testEq "(sumUpTo = n -> (n * (n+1)) div 2; sumUpTo 100)" "5050",
  testEq "(fac = n -> if (n==0) 1 else n * fac (n-1); fac 5)" "120",
  testEq "(id = x -> x; id 5)" "5",
  testEq "(compose = a b -> x -> a (b (x)); (compose (_+2) (_*3)) 6)" "20",
  testEq "(list = xs* -> xs; list 5 4)" "[5,4]",
  testEq "(keywordTest = a b -> list a b; keywordTest 5 4)" "[5,4]",
  testEq "(keywordTest = a b -> list a b; keywordTest a=5 b=4)" "[5,4]",
  testEq "(keywordTest = a b -> list a b; keywordTest b=5 a=4)" "[4,5]",
  testEq "((_+2) o (_*3)) 5" "17"
  ]

objTests = TestLabel "obj" $ TestList [
  testEq "(x = {a=5}; x.a)" "5",
  testEq "(x = {a=5}; x.a <- 10; x.a)" "10",
  testEq "(x = {a=5}; y = clone x; y.a <- 10; x.a)" "5",
  testEq "(x = {a=5}; y = clone x; x.a <- 10; y.a)" "5"
  -- These tests won't work until I finish objects
  {-testEq "(x = {a=5}; y = new x {b=4}; y.a <- 10; x.a)" "5",
  testEq "(x = {a=5}; y = new x {b=4}; x.a <- 10; y.a)" "10"-}
  ]

-- These test physical units like meters; the name doesn't mean what 'unit test' normally means
unitTests = TestLabel "unit" $ TestList [
  testEq "5 meters" "500 cm",
  testEq "5 meters + 500 cm" "10 meters",
  testEq "5 m * 2 m" "10 m^2",
  testEq "5 m / 2 m" "2.5",
  testEq "5 m^2" "5 (m^2)",
  testEq "5 thousand" "5000"
  ]

allTests = TestList [arithTests, varTests, fnTests, objTests, unitTests]

runTests = getTestEnv >> runTestTT allTests


testParse parser = forever $ do
  input <- replGetInput Nothing
  lift $ case parse (parser <* eof) "test" input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right expr -> print expr

