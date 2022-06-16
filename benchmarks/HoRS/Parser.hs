{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module HoRS.Parser where

import Control.Monad.Reader
import Data.Char
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import HoMSL.Syntax
import Text.Parsec
import Text.Parsec.Token

-- | An automaton transition.
data Transition = Transition
  { state :: String,
    symbol :: String,
    children :: IntMap.IntMap String
  }
  deriving stock (Show)

-- | Non-terminal production rule.
data Rule
  = Rule String [String] (Term String)
  deriving stock (Show)

-- TODO: Sort inference.

-- | Parse a combined HoRS problem.
parseHoRS :: String -> ([Rule], [Transition])
parseHoRS str =
  case runReader (runParserT (pHoRS <* eof) () "" str) mempty of
    Left err -> error (show err)
    Right fs -> fs

lexer :: GenTokenParser String u (Reader (HashSet.HashSet String))
lexer =
  makeTokenParser $
    LanguageDef
      { commentStart = "",
        commentEnd = "",
        commentLine = "",
        nestedComments = True,
        identStart = letter,
        identLetter = alphaNum,
        opStart = oneOf ".,-",
        opLetter = oneOf ".,->",
        reservedOpNames = ["->", ".", ",", "="],
        reservedNames = ["%BEGINA", "%BEGING", "%ENDA", "%ENDG"],
        caseSensitive = True
      }

-- | Parse a combined HoRS problem.
pHoRS :: ParsecT String u (Reader (HashSet.HashSet String)) ([Rule], [Transition])
pHoRS = do
  reserved lexer "%BEGING"
  r <- sepEndBy pRule (reservedOp lexer ".")
  reserved lexer "%ENDG"

  reserved lexer "%BEGINA"
  t <- sepEndBy pTransition (reservedOp lexer ".")
  reserved lexer "%ENDA"
  pure (r, t)

-- | Parse an automaton transition.
pTransition :: ParsecT String u (Reader (HashSet.HashSet String)) Transition
pTransition = do
  q <- identifier lexer
  f <- identifier lexer
  reservedOp lexer "->"

  xs <-
    many1
      ( parens lexer $ do
          i <- decimal lexer
          reservedOp lexer ","
          q <- identifier lexer
          pure (fromInteger i, q)
      )
      <|> do
        qs <- many1 (identifier lexer)
        pure (zip [1 ..] qs)
      <|> pure []

  pure (Transition q f $ IntMap.fromList xs)

-- | Parse a production rule.
pRule :: ParsecT String u (Reader (HashSet.HashSet String)) Rule
pRule = do
  f <- identifier lexer
  xs <- many (identifier lexer)
  reservedOp lexer "="
  rhs <- local (HashSet.fromList xs <>) pTerm
  pure (Rule f xs rhs)

-- | Parse an applicative term.
pTerm :: ParsecT String u (Reader (HashSet.HashSet String)) (Term String)
pTerm = chainl1 inner (pure App) <?> "term"
  where
    inner :: ParsecT String u (Reader (HashSet.HashSet String)) (Term String)
    inner =
      parens lexer pTerm
        <|> do
          f <- identifier lexer
          if isLower (head f)
            then
              asks (HashSet.member f) >>= \case
                False -> pure (Sym f)
                True -> pure (Var f)
            else pure (Sym f)
