module HoRS.Parser where

import qualified Data.IntMap as IntMap
import Text.Parsec
import Text.Parsec.Token

-- TODO: Where do we get type information from??

-- | An automaton transition.
data Transition = Transition
  { state :: String,
    symbol :: String,
    children :: IntMap.IntMap String
  }

-- | Non-terminal production rule.
data Rule = Rule {
  nonTerminal :: String,
  args :: [String],
  rhs :: Term
}

-- | Parse an automaton transition.
pTransition :: Parsec String u Transition
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

pRule :: Parsec String u Rule

lexer :: TokenParser u
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
        reservedOpNames = ["->", ".", ","],
        reservedNames = [],
        caseSensitive = True
      }