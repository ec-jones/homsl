{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

-- | HoRS Syntax and convertion to HoMSL
module HoRS.Syntax
  ( -- * Syntax
    Transition (..),
    Rule (..),
    parseHoRS,
  )
where

import Control.Monad.Reader
import Data.Char
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import HoMSL.Syntax
import Text.Parsec
import Text.Parsec.Token

-- * HoRS Syntax

-- | An automaton transition.
data Transition = Transition
  { state :: String,
    symbol :: String,
    rhs :: IntMap.IntMap (HashSet.HashSet String)
  }
  deriving stock (Show)

-- | Non-terminal production rule.
data Rule
  = Rule String [String] (Term String)
  deriving stock (Show)

-- * Parser

-- | Parse a @.hrs@ file.
parseHoRS :: String -> ([Rule], [Transition])
parseHoRS str =
  case runReader (runParserT (whiteSpace lexer *> pHoRS <* eof) () "" str) mempty of
    Left err -> error (show (str, err))
    Right (rules, trans) -> (rules, trans)

-- | Lexer for HoRS syntax.
lexer :: GenTokenParser String u (Reader (HashSet.HashSet String))
lexer =
  makeTokenParser $
    LanguageDef
      { commentStart = "/*",
        commentEnd = "*/",
        commentLine = "//",
        nestedComments = False,
        identStart = letter,
        identLetter = alphaNum <|> char '_',
        opStart = oneOf ".,-",
        opLetter = oneOf ".,->",
        reservedOpNames = ["->", ".", ",", "=", "->."],
        reservedNames = ["%BEGINA", "%BEGING", "%ENDA", "%ENDG"],
        caseSensitive = True
      }

-- | Parse a combined HoRS problem.
pHoRS :: ParsecT String u (Reader (HashSet.HashSet String)) ([Rule], [Transition])
pHoRS = do
  reserved lexer "%BEGING"
  r <- many pRule
  reserved lexer "%ENDG"

  reserved lexer "%BEGINA"
  t <- many pTransition
  reserved lexer "%ENDA"
  pure (r, t)

-- | Parse an automaton transition.
pTransition :: ParsecT String u (Reader (HashSet.HashSet String)) Transition
pTransition = do
  q <- identifier lexer
  f <- identifier lexer
  (do
      reservedOp lexer "->"

      rhs <-
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

      reservedOp lexer "."

      pure (Transition q f $ fmap HashSet.singleton $ IntMap.fromList rhs)
    ) <|>
      (do
            reservedOp lexer "->."
            pure (Transition q f IntMap.empty)
      )


-- | Parse a production rule.
pRule :: ParsecT String u (Reader (HashSet.HashSet String)) Rule
pRule = do
  f <- identifier lexer
  xs <- many (identifier lexer)
  (reservedOp lexer "=" <|> reservedOp lexer "->")
  rhs <- local (HashSet.fromList xs <>) pTerm
  reservedOp lexer "."
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
