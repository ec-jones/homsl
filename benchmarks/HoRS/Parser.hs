{-# LANGUAGE LambdaCase #-}

module HoRS.Parser where

import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import qualified Data.HashSet as HashSet 
import Text.Parsec
import Text.Parsec.Token
import HoMSL.Syntax
import Data.Char

-- | An automaton transition.
data Transition = Transition
  { state :: String,
    symbol :: String,
    children :: IntMap.IntMap String
  }

-- | Non-terminal production rule.
data Rule =
  Rule String [String] (Term String)

-- TODO: Sort inference.

-- | Parse an automaton transition.
pTransition :: ParsecT String u (Reader (HashSet.HashSet String)) Transition
pTransition = do
  q <- identifier lexer
  f <- identifier lexer
  reservedOp lexer "->"

  xs <-
    many
      ( parens lexer $ do
          i <- decimal lexer
          reservedOp lexer ","
          q <- identifier lexer
          pure (fromInteger i, q)
      )
      <|> do
        qs <- many (identifier lexer)
        pure (zip [1 ..] qs)

  reservedOp lexer "."
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
pTerm :: ParsecT String u (Reader (HashSet.HashSet String))  (Term String)
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
                True ->pure (Var f)
            else pure (Sym f)

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
        reservedNames = [],
        caseSensitive = True
      }