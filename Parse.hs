{-# LANGUAGE TupleSections #-}

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
import Text.Parsec.Expr

import Util

import Expr
import Eval

parseStatement = parseExec <|> parseVarDef <|> try parseDef <|> tryParseAssign

parseExec = do
  symbol "\\"
  str <- some (noneOf separators)
  pure (EFnApp (eId "execRaw") [Arg $ makeString str])

tryParseAssign = do
  expr <- parseExpr
  (EAssign expr <$> (symbol "<-" *> parseExpr)) <|> pure expr

identifier' = do
  accessType <- (symbol "~" *> pure ByName) <|> pure ByVal
  id <- identifier
  pure (id,accessType)

parseDef = do
  id <- identifier
  let
    parseValDef = EDef id <$> (wholeSymbol "=" *> parseExpr)
    parseFnDef = do
      params <- many parseParam
      body <- (if not (null params) then wholeSymbol "=" *> parseExpr else mzero) <|> symbol "->" *> parseExpr
      pure $ EDef id (EFn params body)
  parseValDef <|> parseFnDef


parseVarDef = do
  name <- symbol "var" *> identifier
  val <- (symbol "<-" *> parseExpr) <|> pure EVoid
  pure $ EVarDef name val

separators = ";,\n"
separator = lexeme (oneOf separators)
parseBlock = EBlock <$> block
block = symbol "{" *> many separator *> sepEndBy parseStatement (some separator) <* symbol "}"
parseCompound = many separator *> sepEndBy parseStatement (some separator)


parseParam = asum [parseOptParam, try parseRepParam, parseReqParam]
parseOptParam = OptParam <$> (symbol "?" *> identifier') <*> (symbol ":" *> parseExpr)
parseRepParam = RepParam <$> identifier' <* symbol "*"
parseReqParam = ReqParam <$> identifier'

parseExpr = parsePipes
parseNonPipeExpr = parseIf <|> parseNonIf
parseNonIf = buildExpressionParser opTable parseWith
parseNonWithExpr = parseFnApp
parseNonFnAppExpr = parseMemberAccess
parseNonMemberAccess = parseNew <|> parseSingleTokenExpr

parseSingleTokenExpr = asum [parseBlock, parseParens, parseList, parseFloat, parseInt, parseVoid, parseString '"', parseString '\'', parseChar, parseBool, EId <$> identifier']

parsePipes = do
  start <- parseNonPipeExpr
  xs <- chainl ((:[]) <$> ((,) <$> (symbol "|" *> identifier) <*> many parseArg)) (pure (++)) []
  let
    f obj (id,[]) = EMemberAccess obj id
    f obj (id,args) = EFnApp (EMemberAccess obj id) args
  pure $ foldl f start xs

parseParens = between (symbol "(") (symbol ")") parseExpr
parseList = makeList <$> (symbol "[" *> many separator *> sepEndBy parseExpr (some separator) <* symbol "]")

parseFnApp = parseNormalFnApp <|> parsePrefixOp
parseNormalFnApp = do
  first <- parseNonFnAppExpr
  (EFnApp first <$> some parseArg) <|> pure first
parsePrefixOp = EFnApp <$> (eId <$> operator') <*> ((:[]) <$> parseArg) --TODO: this used to say "some parseArg", but prefix operators can only take 1 argument
parseArg = do
  first <- try parseNonFnAppExpr
  let
    parseKeywordArg = do
      symbol ":"
      case first of
        EId (id,_) -> KeywordArg id <$> parseNonFnAppExpr
        _ -> mzero
  parseKeywordArg <|> pure (Arg first)

parseMemberAccess = do
  first <- parseNonMemberAccess
  (EMemberAccess first <$> (symbol "." *> identifier)) <|> pure first

parseNew = ENew <$> (symbol "new" *> block)
parseWith = do
  obj <- parseNonWithExpr
  let withArg = (ENew <$> block) <|> parseNonWithExpr
  xs <- chainl ((:[]) <$> (symbol "with" *> withArg)) (pure (++)) []
  pure $ foldl EWith obj xs

parseIf = do
  cond <- symbol "if" *> parseSingleTokenExpr
  t <- parseNonIf
  f <- parseElse <|> pure EVoid
  pure (EIf cond t f)
parseElse = symbol "else" *> parseExpr

parseFn = do
  params <- many parseParam
  body <- symbol "=>" *> parseExpr
  pure (EFn params body)

parseBool = parseTrue <|> parseFalse
parseTrue = symbol "True" *> pure (makeBool True)
parseFalse = symbol "False" *> pure (makeBool False)
parseVoid = symbol "void" *> pure EVoid



opTable = [
  op '*' ++ op '/' ++ op '%',
  op '+' ++ op '-',
  op ':',
  op '=' ++ op '!',
  op '<' ++ op '>',
  op '&',
  op '^',
  op '|'
  ]
op startChar = [binopL startChar, binopR startChar]
binopL startChar = Infix (try $ do
  name <- operator startChar False
  pure (\a b -> EFnApp (EMemberAccess a name) [Arg b])
  ) AssocLeft
binopR startChar = Infix (try $ do
  name <- operator startChar True
  pure (\a b -> EFnApp (EMemberAccess b name) [Arg a]) --We swap a and b here intentionally
  ) AssocRight

reservedOps = ["|", "~", "=", "->", "=>", "<-", "?", "\\"]
keywords = ["True", "False", "new", "with", "void", "if", "else", "var"]

identStart = satisfy isAlpha
identChar = satisfy isAlphaNum

identifier = (do
  val <- lexeme $ (:) <$> identStart <*> many identChar
  if val `elem` keywords then mzero else pure val) <?> "identifier"

opChars = "/<>?:\\|`~!@#$%^&*_+-="


operator' = (do
  val <- lexeme $ some $ satisfy (`elem` opChars)
  if val `elem` reservedOps then mzero else pure val) <?> "operator"


operator startChar rassoc = (do
  char startChar
  val <- lexeme $ many (oneOf opChars)
  let str = startChar : val
  if rassoc /= (last str == ':') || str `elem` reservedOps then mzero else pure str
  ) <?> "operator"


--- Non-language-specific parsing stuff ---

parseInt = makeInt <$> integer
parseFloat = makeFloat <$> float
parseChar = makeChar <$> lexeme (char '#' *> character)
parseString bound = makeString  <$> (char bound *> many (character' [bound]) <* char bound <* whiteSpace)
character' omit = escapeChar <|> noneOf omit
character = escapeChar <|> anyChar
escapeChar = char '\\' *> asum (for escapeChars $ \(c,v) -> char c *> pure v)
escapeChars = [
  ('n', '\n'),
  ('t', '\t'),
  ('\'', '\''),
  ('"', '"'),
  ('\'', '\'')
  ]

parseWholeInput = between whiteSpace eof


symbol = lexeme . string
--wholeSymbol is sometimes useful, but it makes a lot of assumptions about the nature of the given symbol. It can't be used everywhere because it conflicts with parens and other symbols that can be right next to each other - those particular symbols could be handled specially
wholeSymbol str = lexeme $ do
  let f = if isAlphaNum (head str) then satisfy isAlphaNum else satisfy (\x -> not (isAlphaNum x || isSpace x))
  str' <- some f
  if str==str' then pure str else mzero
lexeme p = try p <* whiteSpace

--We don't allow newlines as whitespace because they are statement separators
whiteSpace = skipMany (void (oneOf " \t") <|> oneLineComment <|> multiLineComment) <?> "whitespace"

commentLine = "//"
commentStart = "/*"
commentEnd = "*/"

oneLineComment = do
  try $ string commentLine
  skipMany (satisfy (/= '\n'))

multiLineComment = do
  try $ string commentStart
  inComment

inComment =
  try (string commentEnd >> pure ()) <|>
  (multiLineComment >> inComment) <|>
  (skipMany1 (noneOf startEnd) >> inComment) <|>
  (oneOf startEnd >> inComment)
  where
    startEnd = nub $ commentEnd ++ commentStart



float = lexeme floating <?> "float"

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
integer = lexeme (try prefixNumber <|> decimal) <?> "integer"

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
