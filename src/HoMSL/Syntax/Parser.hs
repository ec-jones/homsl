{-# LANGUAGE LambdaCase #-}

module HoMSL.Syntax.Parser (
    parseProgram, parseFormula
    ) where

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

parseFormula :: String -> Formula
parseFormula str =
  case runReader  ( runParserT pBody 0 "" str ) mempty of
    Left err -> error (show err)
    Right fs -> fs

-- | Lexer for Haskell style tokens.
lexer :: GenTokenParser String Int (Reader (HashMap.HashMap String Id))
lexer =
  makeTokenParser $
    LanguageDef
      { commentStart = "{-",
        commentEnd = "-}",
        commentLine = "--",
        nestedComments = True,
        identStart = letter,
        identLetter = alphaNum <|> oneOf "_'",
        opStart = oneOf "</;",
        opLetter = oneOf "<=/\\.;-",
        reservedOpNames = ["<=", "/\\", ".", ":", ";", "->"],
        reservedNames = ["i", "o"],
        caseSensitive = True
      }

-- | Parse a clause.
pClause :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Formula
pClause = do
  xs <-
    ( do
        reserved lexer "forall"
        xs <- many pIdenDecl
        reservedOp lexer "."
        pure xs
      )
      <|> pure []

  local (HashMap.fromList [(idName x, x) | x <- xs] <>) $ do
    head <- pHead

    body <-
      ( do
          reservedOp lexer "<="
          pBody
        )
        <|> pure (Conj [])

    let (us, es) = List.partition (`IdEnv.member` IdEnv.freeVars head) xs
        body' = foldl' (flip Exists) body es

    pure (Clause (toList us) head body')

-- | Parse the head of a clause.
pHead :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Formula
pHead = Atom <$> pTerm

-- | Parse the body of a clause.
pBody :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Formula
pBody =
  Conj <$> sepEndBy pAtom (reservedOp lexer "/\\") <?> "body"
  where
    pAtom :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Formula
    pAtom =
      try (Atom <$> pTerm) <|>
        pClause

-- | Parse an applicative term.
pTerm :: ParsecT String Int (Reader (HashMap.HashMap String Id)) (Term Id)
pTerm = chainl1 inner (pure App) <?> "term"
  where
    inner :: ParsecT String Int (Reader (HashMap.HashMap String Id)) (Term Id)
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

-- | Parse a declaration of a local identifier.
pIdenDecl :: ParsecT String Int (Reader (HashMap.HashMap String Id)) Id
pIdenDecl = parens lexer $ do
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
