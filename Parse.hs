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
import qualified Text.Parsec as Parsec
import Text.Parsec.Expr

import Util

import Expr
import Eval

tryParseAssign = do
  expr <- parseNonStatement
  let
    parseAssign = do
      val <-  symbol "<-" *> parseExpr
      case getVar expr of
        Just var -> pure $ EAssign var val
        Nothing -> mzero
  parseAssign <|> pure expr

identifier' = do
  accessType <- (symbol "~" *> pure ByName) <|> pure ByVal
  id <- identifier
  pure (id,accessType)

parseDef = do
  id <- identifier
  let
    parseValDef = EDef id <$> (symbol "=" *> parseExpr)
    parseFnDef = do
      params <- parseParams
      body <- symbol "->" *> parseExpr
      pure $ EDef id (EFn params body)
  parseValDef <|> parseFnDef


parseVarDef = do
  name <- keyword "var" *> identifier
  val <- (symbol "<-" *> parseExpr) <|> pure EVoid
  pure $ EVarDef name val

separators = ";,\n"
separator = lexeme (oneOf separators)
parseBlock = EBlock <$> block
block = grouper '{' *> many separator *> sepEndBy parseExpr (some separator) <* grouper '}'
parseCompound = many separator *> sepEndBy parseExpr (some separator)


parseParams = parseParams' <|> pure [] where
  parseParams' = ((:) <$> parseOptParam <*> parseParams) <|> ((:[]) <$> try parseRepParam) <|> ((:) <$> parseReqParam <*> parseParams)
  parseOptParam = OptParam <$> (symbol "?" *> identifier') <*> (symbol "=" *> parseExpr)
  parseRepParam = RepParam <$> identifier' <* symbol "*"
  parseReqParam = ReqParam <$> identifier'




parseExpr = parseVarDef <|> try parseDef <|> tryParseAssign

parseNonStatement = parseExec <|> parsePipes
parseNonPipeExpr = parseIf <|> parseNonIf
parseNonIf = buildExpressionParser opTable parseWith
parseNonWithExpr = try parseFn <|> parseFnApp
parseNonFnAppExpr = parseNew <|> parseSingleTokenExpr

parseSingleTokenExpr = parseMemberAccess
parseNonMemberAccess = parseOtherExpr
parseOtherExpr = asum [parseBlock, parseTuple, parseList, parseFloat, parseInt, parseVoid, parseUnknown, parseString '"', parseString '\'', parseChar, parseBool, EId <$> identifier']

parseUnknown = symbol "_" *> pure EUnknown

parseExec = do
  symbol "/"
  str <- some (noneOf separators) --TODO: this doesn't support comments!
  pure (EFnApp (eId "execRaw") [Arg $ makeString str])


parsePipes = do
  start <- parseNonPipeExpr
  xs <- chainl ((:[]) <$> ((,) <$> (symbol "|" *> identifier) <*> parseArgs)) (pure (++)) []
  let
    f obj (id,args) = EFnApp (EMemberAccess obj id) args
  pure $ foldl f start xs

parseList = makeList' <$> (grouper '[' *> sepEndBy parseExpr separator <* grouper ']')
parseTuple = do
  first <- grouper '(' *> parseExpr
  (grouper ')' *> pure first) <|> (makeTuple' . (first:) <$> (separator *> sepEndBy parseExpr separator <* grouper ')'))

parseFnApp = parseNormalFnApp <|> parsePrefixOp
parseNormalFnApp = do
  fn <- parseNonFnAppExpr
  args <- parseArgs
  pure (EFnApp fn args)

parsePrefixOp = EFnApp <$> (eId <$> operator') <*> ((:[]) <$> parseArg)
parseArg = do
  first <- try parseNonFnAppExpr
  let
    parseListArg = ListArg <$> (symbol "*" *> pure first)
    parseKeywordArg = do
      symbol ":"
      case first of
        EId (id,_) -> KeywordArg id <$> parseNonFnAppExpr
        _ -> mzero
  parseListArg <|> parseKeywordArg <|> pure (Arg first)

parseArgs = do
  args <- many parseArg
  (args++) <$> ((symbol "_*" *> pure [RestArgs]) <|> pure [])

parseMemberAccess = do
  first <- parseNonMemberAccess
  (EMemberAccess first <$> (symbol "." *> identifier)) <|> pure first

parseNew = ENew <$> (keyword "new" *> block)
parseWith = do
  obj <- parseNonWithExpr
  let withArg = (ENew <$> block) <|> parseNonWithExpr
  xs <- chainl ((:[]) <$> (keyword "with" *> withArg)) (pure (++)) []
  pure $ foldl EWith obj xs

parseIf = do
  cond <- keyword "if" *> parseSingleTokenExpr
  t <- parseNonIf
  f <- parseElse <|> pure EVoid
  pure (EIf cond t f)
parseElse = anyWhiteSpace *> keyword "else" *> parseExpr

parseFn = do
  params <- parseParams
  body <- symbol "=>" *> parseExpr
  pure (EFn params body)

parseBool = parseTrue <|> parseFalse
parseTrue = keyword "True" *> pure (makeBool True)
parseFalse = keyword "False" *> pure (makeBool False)
parseVoid = keyword "void" *> pure EVoid



opTable = [
  op '*' ++ op '/' ++ op '%',
  op '+' ++ op '-',
  op ':',
  op '=' ++ op '!',
  op '<' ++ op '>',
  op '&',
  op '^',
  op '|',
  --TODO: figure out precedence of these chars:
  op '?' ++ op '\\' ++ op '`' ++ op '~' ++ op '@' ++ op '#' ++ op '$' ++ op '_'
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

reservedOps = ["|", "~", "=", "->", "=>", "<-", "?", "\\", ":", "_", "_*", "."]
builtinOps = reservedOps ++ ["*", "/"]
keywords = ["True", "False", "new", "with", "void", "if", "else", "var"]

groupChars = "()[]{}"

identStart = satisfy isAlpha
identChar = satisfy (\x -> isAlphaNum x || x=='\'')

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

keyword str = assert (str `elem` keywords) $ lexeme (string str <* notFollowedBy (satisfy isAlphaNum))
symbol str = assert (str `elem` builtinOps) $ lexeme (string str <* notFollowedBy (satisfy $ (`elem` opChars)))
grouper c = assert (c `elem` groupChars) $ lexeme (char c)

lexeme p = try p <* whiteSpace

--We don't allow newlines as whitespace because they are statement separators; the symbol' "\" followed by a newline must be used instead
whiteSpace = whiteSpace' " \t"
anyWhiteSpace = whiteSpace' " \t\n"

whiteSpace' :: String -> Parsec String () ()
whiteSpace' whitespace = skipMany (void (oneOf whitespace) <|> oneLineComment <|> multiLineComment <|> void (lexeme $ string "\\\n")) <?> "whitespace"

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
