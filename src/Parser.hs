{-# LANGUAGE LambdaCase #-}

module Parser (parseProgram) where

import Control.Monad.Reader
import Data.Char
import Data.Foldable
import Data.Hashable
import qualified Data.List as List
import Syntax
import Text.Parsec
import Text.Parsec.Token

-- | Parse a collection of symbol declarations and clauses.
parseProgram :: String -> [Formula]
parseProgram str =
  case runReader
    ( runParserT
        (sepEndBy pClause (reservedOp lexer ";") <* eof)
        ()
        ""
        str
    )
    mempty of
    Left err -> error (show err)
    Right fs -> fs

-- | Lexer for Haskell style tokens.
lexer :: GenTokenParser String () (Reader Scope)
lexer =
  makeTokenParser $
    LanguageDef
      { commentStart = "{-",
        commentEnd = "-}",
        commentLine = "--",
        nestedComments = True,
        identStart = letter,
        identLetter = alphaNum <|> oneOf "_'",
        opStart = oneOf "<=/.;:-",
        opLetter = oneOf "<=/\\.;:->",
        reservedOpNames = ["<=", "/\\", ".", ":", ";", "->"],
        reservedNames = ["false", "forall", "i", "o"],
        caseSensitive = True
      }

-- | Parse a clause.
pClause :: ParsecT String () (Reader Scope) Formula
pClause = do
  -- Collect binders
  xs <-
    ( do
        reserved lexer "forall"
        xs <- many (pSymbolDec True)
        reservedOp lexer "."
        pure xs
      )
      <|> pure []

  -- Extend scope for parsing body and head
  local (mkScope xs <>) $ do
    -- Head is either atom or false.
    head <- (Ff <$ reserved lexer "false") <|> pAtom
    ( do
        reservedOp lexer "<="

        -- Body is a conjunction of atoms.
        body <- sepBy1 pAtom (reservedOp lexer "/\\")

        -- Partition variables into truly universal and existential.
        let (us, es) = List.partition (`inScope` freeVars head) xs
            body' = foldl' (flip Exists) (Conj body) es

        pure (Clause us body' head)
      )
      <|> ( do
              -- Facts
              let us = List.filter (`inScope` freeVars head) xs
              pure (Clause us (Conj []) head)
          )

-- | Parse an atomic formula.
pAtom :: ParsecT String () (Reader Scope) Formula
pAtom = Atom <$> pTerm

-- | Parse an applicative term.
-- pTerm :: Parsec String u Term
pTerm :: ParsecT String () (Reader Scope) Term
pTerm = chainl1 inner (pure App) <?> "term"
  where
    inner :: ParsecT String () (Reader Scope) Term
    inner =
      parens lexer pTerm
        <|> do
          f <- identifier lexer
          if isLower (head f)
            then do
              asks (lookupFromUnique (hash f)) >>= \case
                Nothing -> error ("Variable not in scope: " ++ show f)
                Just x -> pure (Var x)
            else pure (Sym f)

-- | Parse a declaration of a function symbol.
pSymbolDec :: Bool -> ParsecT String () (Reader Scope) Id
pSymbolDec p = (if p then (parens lexer) else id) $ do
  x <- identifier lexer
  reservedOp lexer ":"
  s <- pSort
  pure (Id x s (hash x))

-- | Parse a simple type over proposition and trees.
pSort :: ParsecT String () (Reader Scope) Sort
pSort = chainr1 inner ((:->) <$ reservedOp lexer "->") <?> "sort"
  where
    inner :: ParsecT String () (Reader Scope) Sort
    inner =
      parens lexer pSort
        <|> I <$ reserved lexer "i"
        <|> O <$ reserved lexer "o"