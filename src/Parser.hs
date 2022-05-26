{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Parser (parseClauses, parseFormula) where

import Binder
import Control.Monad
import Data.Char
import Data.HashSet qualified as HashSet
import Syntax
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

parseClauses :: String -> [Formula]
parseClauses str =
  let ?scope = HashSet.empty
   in case parse
        ( whiteSpace lexer
            *> sepEndBy pClause (reservedOp lexer ";")
            <* eof
        )
        ""
        str of
        Left err -> error (show err)
        Right fm -> fm

parseFormula :: String -> Formula
parseFormula str =
  let ?scope = HashSet.empty
   in case parse
        ( whiteSpace lexer
            *> pFormula
            <* eof
        )
        ""
        str of
        Left err -> error (show err)
        Right fm -> fm

-- | Lexer for Haskell style tokens.
lexer :: TokenParser s
lexer =
  makeTokenParser
    haskellStyle
      { reservedNames = ["forall", "true", "exists"],
        reservedOpNames = ["=>", "/\\", ".", ";"]
      }

pClause :: (?scope :: Scope) => Parser Formula
pClause = do
  xs <-
    ( do
        reserved lexer "forall"
        xs <- many pBinder
        reservedOp lexer "."
        pure xs
      )
  let ?scope = ?scope `HashSet.union` HashSet.fromList xs
  body <-
    ( do
        body <- pFormula
        reservedOp lexer "=>"
        pure body
      )
  head <- pFormula
  pure (Clause xs body head)

pFormula :: (?scope :: Scope) => Parser Formula
pFormula =
  Conj <$> sepBy1 inner (reservedOp lexer "/\\")
  where
    inner =
      parens lexer pFormula
        <|> pClause
        <|> pExists
        <|> pTrue
        <|> pFalse
        <|> pAtom
          <?> "formula"

pExists :: (?scope :: Scope) => Parser Formula
pExists = do
  reserved lexer "exists"
  x <- pBinder
  let ?scope = ?scope `HashSet.union` HashSet.singleton x
  reservedOp lexer "."
  body <- pFormula
  pure (Exists x body)

pTrue :: Parser Formula
pTrue = do
  reserved lexer "true"
  pure (Conj [])

pFalse :: Parser Formula
pFalse = do
  reserved lexer "false"
  pure Ff

pAtom :: (?scope :: Scope) => Parser Formula
pAtom = Atom <$> pTerm
  where
    pTerm :: Parser Term
    pTerm =
      chainl1
        ( parens lexer pTerm
            <|> do
              x <- identifier lexer
              if isLower (head x)
                then do
                  unless (HashSet.member x ?scope) $
                    error ("Variable is not in scope: " ++ show x)
                  pure (Var x)
                else pure (Sym x)
        )
        (pure App)
        <?> "term"

pBinder :: Parser String
pBinder = do
  x <- identifier lexer
  guard (isLower $ head x)
  pure x