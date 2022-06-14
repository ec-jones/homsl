{-# LANGUAGE LambdaCase #-}

module HoMSL.Syntax.Parser (parseProgram) where

import Control.Monad.Reader
import Data.Char
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List as List
import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax.Formula
import HoMSL.Syntax.Term
import Text.Parsec
import Text.Parsec.Token

-- | Parse a collection of symbol declarations and clauses.
parseProgram :: String -> [Formula]
parseProgram str =
  case runReader
    ( runParserT
        (sepEndBy pClause (reservedOp lexer ";") <* eof)
        0
        ""
        str
    )
    mempty of
    Left err -> error (show err)
    Right fs -> fs

-- | Lexer for Haskell style tokens.
lexer :: GenTokenParser String u (Reader (HashMap.HashMap String Id))
lexer =
  makeTokenParser $
    LanguageDef
      { commentStart = "{-",
        commentEnd = "-}",
        commentLine = "--",
        nestedComments = True,
        identStart = letter,
        identLetter = alphaNum <|> oneOf "_'",
        opStart = oneOf "=/.;:-",
        opLetter = oneOf "=>/\\.;:->",
        reservedOpNames = ["=>", "/\\", ".", ":", ";", "->"],
        reservedNames = ["false", "forall", "i", "o"],
        caseSensitive = True
      }

-- | Parse a clause.
pClause :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Formula
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
  local (HashMap.fromList [(idName x, x) | x <- xs] <>) $ do
    try
      ( do
          -- Body is a conjunction of atoms.
          body <- sepBy1 pAtom (reservedOp lexer "/\\")

          reservedOp lexer "=>"

          -- Head is either atom or false.
          head <- (Ff <$ reserved lexer "false") <|> pAtom

          -- Partition variables into truly universal and existential.
          let (us, es) = List.partition (`IdEnv.member` IdEnv.freeVars head) xs
              body' = foldl' (flip Exists) (Conj body) es

          pure (Clause us body' head)
      )
      <|> ( do
              -- Facts
              head <- pAtom
              let us = List.filter (`IdEnv.member` IdEnv.freeVars head) xs
              pure (Clause us (Conj []) head)
          )

-- | Parse an atomic formula.
pAtom :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Formula
pAtom = Atom <$> pTerm

-- | Parse an applicative term.
pTerm :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Term
pTerm = chainl1 inner (pure App) <?> "term"
  where
    inner :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Term
    inner =
      parens lexer pTerm
        <|> do
          f <- identifier lexer
          if isLower (head f)
            then do
              asks (HashMap.lookup f) >>= \case
                Nothing -> error ("Variable not in scope: " ++ show f)
                Just x -> pure (Var x)
            else pure (Sym f)

-- | Parse a declaration of a function symbol.
pSymbolDec :: Bool -> ParsecT String Int (Reader (HashMap.HashMap String Id)) Id
pSymbolDec p = (if p then parens lexer else id) $ do
  x <- identifier lexer
  reservedOp lexer ":"
  s <- pSort
  unique <- getState
  putState (unique + 1)
  pure (Id x s unique)

-- | Parse a simple type over proposition and trees.
pSort :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Sort
pSort = chainr1 inner ((:->) <$ reservedOp lexer "->") <?> "sort"
  where
    inner :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Sort
    inner =
      parens lexer pSort
        <|> I <$ reserved lexer "i"
        <|> O <$ reserved lexer "o"
