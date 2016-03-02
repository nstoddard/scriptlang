{-# LANGUAGE TupleSections, FlexibleContexts #-}

{-
  Each parser should parse only the stated expression, with no whitespace on either side. This is necessary in order to support the operator syntax I want.
-}

module Parse where

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
import qualified Text.Parsec as Parsec
import Text.Parsec.Expr

import Util hiding (try, (</>), Infix)

import Expr
import Eval

tryParseAssign = do
  expr <- parseNonStatement
  let
    parseAssign = do
      val <- try (whitespace *> symbol "<-") /> parseExpr
      case getVar expr of
        Just var -> pure $ EAssign var val
        Nothing -> mzero
  parseAssign <|> pure expr

identifier' = do
  accessType <- (symbol "~" *> pure ByName) <|> pure ByVal
  id <- identifier
  pure (id,accessType)

statementSeparator = inWhitespace $ oneOf ";,\n"
listSeparator = oneOf ";,"

block start end = between (grouper start) (grouper end) parseCompound
parseCompound = sepStartEndBy (inWhitespace parseExpr) (some statementSeparator)

sepStartEndBy parser sep = many sep *> sepEndBy parser sep




parseExpr = parseUnitDef <|> try parseDef <|> tryParseAssign

parseUnitDef = do
  utype <- (tryString "si-unit" *> pure USI) <|>
    (tryString "bin-unit" *> pure UBin) <|>
    (tryString "unit" *> pure UNormal)
  names <- whitespace *> sepBy1 identifier (char '/')
  whitespace
  abbrs <- option [] $ try (char '(' /> sepBy1 identifier (char '/') </ char ')')
  whitespace
  value <- option Nothing $ Just <$> (char '=' /> parseExpr <* whitespace)
  pure $ EUnitDef utype names abbrs value


parseNonStatement = parseExec <|> parsePipes
parseNonPipeExpr = parseIf <|> parseNonIf
parseNonIf = buildExpressionParser opTable (parseClone <|> parseNew' <|> parseNonWithExpr)
parseNonWithExpr = try parseFn <|> parseFnApp
parseNonFnAppExpr = parseSingleTokenExpr

parseSingleTokenExpr = parseMemberAccess
parseNonMemberAccess = parseOtherExpr
parseOtherExpr = asum [parseMakeObj, EBlock <$> block '(' ')', parseList, parseFloat, parseInt, parseVoid, parseUnknown, parseString '"', parseString '\'', parseChar, parseBool, EId <$> identifier']

parsePipes = do
  start <- parseNonPipeExpr
  xs <- chainl ((:[]) <$> ((,) <$> try (whitespace *> symbol "|" /> (EId <$> identifier')) </> parseArgs)) (pure (++)) []
  let
    f obj (id,args) = EFnApp id (args++[Arg obj])  --EFnApp (EMemberAccess obj id) args
  pure $ foldl f start xs

parseList = makeList' <$> (grouper '[' *> sepBy (inAnyWhitespace parseExpr) listSeparator <* grouper ']')
parseParens = grouper '(' *> inAnyWhitespace parseExpr <* grouper ')'

parseClone = EClone <$> (keyword "clone" /> parseSingleTokenExpr)

parseNew' = do
  keyword "new"
  xs <- chainl1 ((:[]) <$> try (whitespace *> parseSingleTokenExpr)) (pure (++))
  pure $ ENew' xs


parseMakeObj = EMakeObj <$> block '{' '}'

ops = [
  "^",
  "*/%",
  "+-",
  ":",
  "=!",
  "<>",
  "&",
  "|",
  "?\\~@#$"
  ]

opTable = map (concatMap $ op False) ops ++ map (concatMap $ op True) ops

op reqSpaces startChar = [binopL startChar reqSpaces, binopR startChar reqSpaces]
binopL startChar reqSpaces = Infix (try $ do
  when reqSpaces someWhitespace
  name <- operator startChar False
  when reqSpaces someWhitespace
  pure (\a b -> EFnApp (EMemberAccess a name) [Arg b])
  ) AssocLeft
binopR startChar reqSpaces = Infix (try $ do
  when reqSpaces someWhitespace
  name <- operator startChar True
  when reqSpaces someWhitespace
  pure (\a b -> EFnApp (EMemberAccess a name) [Arg b]) --We swap a and b here intentionally
  ) AssocRight



prefixOperator = (do
  val <- some $ satisfy (`elem` opChars)
  if val `elem` reservedOps then mzero else pure val) <?> "operator"


operator startChar rassoc = (do
  char startChar
  val <- many (oneOf opChars)
  let str = startChar : val
  if not rassoc && str == "^" then mzero
  else if rassoc && str == "^" then pure str else do
  if rassoc /= (last str == ':') || str `elem` reservedOps then mzero else pure str
  ) <?> "operator"



--This can't use "symbol" because of cases like "_+5"
parseUnknown = tryString "_" *> pure EUnknown


parseDef = do
  id <- identifier <* whitespace
  EDef id <$> (symbol "=" /> parseExpr)

parseFn = parseFn' <|> parseNullaryFn
parseFn' = eFn <$> parseSomeParams </> (symbol "->" /> parseExpr)
parseNullaryFn = eFn [] <$> (symbol "->" /> parseExpr)

parseParams = parseSomeParams <|> pure []

parseSomeParams = ((:) <$> parseOptParam </> parseParams) <|> ((:[]) <$> try parseRepParam) <|> ((:) <$> try parseFlagParam </> parseParams) <|> ((:) <$> parseReqParam </> parseParams) where
  parseOptParam = OptParam <$> (symbol "?" *> identifier') <*> (symbol "=" *> parseExpr)
  parseRepParam = RepParam <$> identifier' <* symbol "*"
  parseReqParam = ReqParam <$> identifier'
  parseFlagParam = FlagParam <$> identifier <* symbol "?"


parseMemberAccess = do
  first <- parseNonMemberAccess
  (EMemberAccess first <$> (symbol "." *> identifier)) <|> pure first

parseFnApp = parseNormalFnApp <|> parsePrefixOp
parseNormalFnApp = EFnApp <$> parseNonFnAppExpr <*> parseArgs
parsePrefixOp = EFnApp <$> (eId <$> prefixOperator) <*> ((:[]) <$> parseArg)
--TODO: this could be made cleaner by not parsing whitespace before the argument
parseArg = try (parseLongFlagArg <|> parseFlagArg <|> (whitespace *> do
  first <- try parseNonFnAppExpr
  let
    parseListArg = ListArg <$> (symbol "*" *> pure first)
    parseKeywordArg = do
      symbol "="
      case first of
        EId (id,_) -> KeywordArg id <$> parseNonFnAppExpr
        _ -> mzero
  parseListArg <|> parseKeywordArg <|> pure (Arg first)))
parseLongFlagArg = LongFlagArg <$> try (someWhitespace *> symbol "--" *> identifier)
parseFlagArg = FlagArg <$> try (someWhitespace *> symbol "-" *> some (noneOf spaceChars))
parseArgs = do
  args <- many parseArg
  (args++) <$> ((symbol "_*" *> pure [RestArgs]) <|> pure [])


identStart = satisfy isAlpha
identChar = satisfy (\x -> isAlphaNum x || x=='\'')

identifier = backquoteIdentifier <|> (do
  val <- (:) <$> identStart <*> many identChar
  if val `elem` keywords then mzero else pure val) <?> "identifier"

backquoteIdentifier = char '`' *> many (noneOf "`") <* char '`'


parseExec = do
  symbol "/"
  str <- some (noneOf "\n")
  pure (EFnApp (eId "execRaw") [Arg $ makeString str])

parseIf = EIf <$> (keyword "if" /> parseSingleTokenExpr) <*> (anyWhitespace *> parseNonIf) <*> (parseElse <|> pure EVoid)
parseElse = try (anyWhitespace *> keyword "else") *> anyWhitespace *> parseExpr

parseBool = parseTrue <|> parseFalse
parseTrue = keyword "true" *> pure (makeBool True)
parseFalse = keyword "false" *> pure (makeBool False)
parseVoid = keyword "void" *> pure EVoid


parseInt = makeInt <$> integer
parseFloat = makeFloat <$> float <*> pure M.empty
parseChar = makeChar <$> (char '#' *> character)
parseString bound = makeString <$> (char bound *> many (character' [bound]) <* char bound)
character' omit = escapeChar <|> noneOf omit
character = escapeChar <|> anyChar
escapeChar = char '\\' *> asum (for escapeChars $ \(c,v) -> char c *> pure v)
escapeChars = [
  ('n', '\n'),
  ('t', '\t'),
  ('\'', '\''),
  ('"', '"'),
  ('\\', '\\')
  ]


--- Primitives


parseWholeInput parser = inWhitespace parser <* eof

keyword str = assert (str `elem` keywords) $ tryString str <* notFollowedBy (satisfy isAlphaNum)
symbol str = assert (str `elem` builtinOps) $ tryString str <* notFollowedBy (satisfy (`elem` opChars))
grouper c = assert (c `elem` groupChars) $ char c

opChars = "/<>?:\\|~!@#$%^&*+-="
--These are operators that can't be redefined because they're used in the language syntax
reservedOps = ["|", "~", "=", "->", "=>", "<-", "?", "\\", "//", "/*", "*/"]
--These are operators that are used as syntax in some cases, but can be redefined in others
builtinOps = reservedOps ++ ["*", "/", "_", "_*", ".", "-", "--"]
keywords = ["true", "false", "new", "with", "extend", "clone", "void", "if", "else", "var", "unit", "si-unit", "bin-unit"]

groupChars = "()[]{}"

spaceChars = " \t\n"

--- Whitespace

whitespace = skipWhitespace " \t"
anyWhitespace = skipWhitespace spaceChars
someWhitespace = skipReqWhitespace " \t"

inWhitespace = between whitespace whitespace
inAnyWhitespace = between anyWhitespace anyWhitespace

infixl 4 </>, />, </
a /> b = a *> whitespace *> b
a </ b = a <* whitespace <* b
a </> b = a <*> (whitespace *> b)

skipWhitespace :: String -> Parsec String () ()
skipWhitespace chars = skipMany (void (oneOf chars) <|> oneLineComment <|> multiLineComment <|> void (string "\\\n")) <?> "whitespace"

skipReqWhitespace :: String -> Parsec String () ()
skipReqWhitespace chars = skipSome (void (oneOf chars) <|> oneLineComment <|> multiLineComment <|> void (string "\\\n")) <?> "whitespace"

tryString = try . string

commentLine = "//"
commentStart = "/*"
commentEnd = "*/"

oneLineComment = do
  tryString commentLine
  skipMany (satisfy (/= '\n'))

multiLineComment = do
  tryString commentStart
  inComment

inComment =
  (tryString commentEnd >> pure ()) <|>
  (multiLineComment >> inComment) <|>
  (skipSome (noneOf startEnd) >> inComment) <|>
  (oneOf startEnd >> inComment)
  where
    startEnd = nub $ commentEnd ++ commentStart


--- Numbers

float = try floating <?> "float"

floating = fractExponent =<< decimal

fractExponent n = fractExponent' <|> exponentOnly where
  fractExponent' = do
    fract <- fraction
    expo <- option 1.0 exponent'
    pure ((fromInteger n + fract)*expo)
  exponentOnly = do
    expo <- exponent'
    pure (fromInteger n * expo)

exponent' = do
  oneOf "eE"
  power <$> decimal
  where
    power e
      | e < 0 = 1.0/power(-e)
      | otherwise = fromInteger (10^e)

fraction = do
  char '.'
  digits <- some digit
  pure (foldr op 0.0 digits)
  where op d f = (f + fromIntegral (digitToInt d))/10.0

integer :: Parsec String () Integer
integer = (try prefixNumber <|> decimal) <?> "integer"

prefixNumber = char '0' *> (hexadecimal <|> binary <|> octal)

isBinDigit c = c == '0' || c == '1'

binDigit = satisfy isBinDigit <?> "Binary digit"

decimal = number 10 digit
hexadecimal = char 'x' *> number 16 hexDigit
binary = char 'b' *> number 2 binDigit
octal = char 'o' *> number 8 octDigit

number base baseDigit = do
  digits <- some baseDigit
  let n = foldl' (\x d -> base*x + toInteger (digitToInt d)) 0 digits
  seq n (pure n)


--TODO: add to Util
skipSome = skipMany1
