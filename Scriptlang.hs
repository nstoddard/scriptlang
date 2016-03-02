{-# LANGUAGE TupleSections #-}

module Main where

{- new todo
  Did I make the same RAM-consuming mistake I made at first with unitcalc? It might not be so obvious with this app, since the environment is so much smaller.
-}

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

import Prelude
import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Error
import Data.Maybe
import Data.Char
import System.IO.Unsafe
import System.IO.Error hiding (catch)
import Control.Exception hiding (try)
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

import Text.Parsec hiding ((<|>), many, optional, State)
import Text.Parsec.Expr

import System.Console.Haskeline as H
import Control.Concurrent hiding (writeChan)
import Control.Concurrent.BoundedChan

import Util

import Expr
import Parse
import Eval
import Test
import Repl


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
  else case env of
    Left err -> putStrLn err
    Right env -> do
      envRef <- newIORef env
      forM_ args $ \arg -> do
        env <- runErrorT $ runFile arg =<< lift (get envRef)
        case env of
          Left err -> putStrLn err >> exitFailure
          Right env -> envRef $= env

