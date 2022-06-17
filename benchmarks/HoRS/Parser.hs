{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module HoRS.Parser where

import Control.Monad.RWS
import Control.Monad.Reader
import Data.Char
import Data.Foldable
import Data.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import Data.Semigroup
import HoMSL.Syntax
import Text.Parsec
import Text.Parsec.Token

-- * HoRS Syntax

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

-- * Parsing

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

-- * Sort Inference

-- | Sorts with unification variables.
data PSort
  = PI
  | PO
  | PFun PSort PSort
  | PVar Int
  | PSym String
  deriving stock (Eq, Show)

psortArgs :: PSort -> [PSort]
psortArgs PI = []
psortArgs PO = []
psortArgs (PFun s t) =
  s : psortArgs t
psortArgs _ = error "Sort args are unknown!"

-- | Sort variable substitution.
data SortSubst = SortSubst
  { symSubst :: HashMap.HashMap String PSort,
    varSubst :: IntMap.IntMap PSort
  }
  deriving stock Show

instance Semigroup SortSubst where
  theta1 <> theta2 =
    SortSubst
      { symSubst = (apply theta1 <$> symSubst theta2) <> symSubst theta1,
        varSubst = (apply theta1 <$> varSubst theta2) <> varSubst theta1
      }

instance Monoid SortSubst where
  mempty = SortSubst mempty mempty

-- TODO: Use inferred sorts to generated clauses.

-- | Find the sorts of terminals and non-terminals from the HoRS problem.
runInfer :: ([Rule], [Transition]) -> HashMap.HashMap String PSort
runInfer (rules, trans) =
  let ((theta, _), _) =
        execRWS (mapM_ inferRule rules) mempty (mempty, 0)
   in symSubst theta

-- | Infer sorts for a rule.
inferRule :: Rule -> RWS (HashMap.HashMap String PSort) () (SortSubst, Int) ()
inferRule (Rule f xs rhs) = do
  (subst, _) <- get
  case HashMap.lookup f (symSubst subst) of
    Nothing -> do
      ss <- replicateM (length xs) fresh
      unify (PSym f) (foldr PFun PI ss)
      local (HashMap.fromList (zip xs ss) <>) $
        matchTerm rhs PI
    Just t -> do
      let ss = psortArgs t
      local (HashMap.fromList (zip xs ss) <>) $
        matchTerm rhs PI

-- | Infer a term's sort.
inferTerm :: Term String -> RWS (HashMap.HashMap String PSort) () (SortSubst, Int) PSort
inferTerm (Var x) =
  asks (HashMap.lookup x) >>= \case
    Nothing -> error "Variable not in scope!"
    Just s -> pure s
inferTerm (Sym f) = pure (PSym f)
inferTerm (App fun arg) = do
  s <- inferTerm fun
  case s of
    PFun t r -> do
      matchTerm arg t
      pure r
    _ -> do
      t <- inferTerm arg
      r <- fresh
      unify s (PFun t r)
      pure r

-- | Attempt to match a term to a given sort.
matchTerm :: Term String -> PSort -> RWS (HashMap.HashMap String PSort) () (SortSubst, Int) ()
matchTerm (Var x) s =
  asks (HashMap.lookup x) >>= \case
    Nothing -> error "Variable not in scope!"
    Just t -> unify t s
matchTerm (Sym f) s =
  unify (PSym f) s
matchTerm (App fun arg) s = do
  t <- inferTerm arg
  matchTerm fun (PFun t s)

-- | Apply a substitution to a sort.
apply :: SortSubst -> PSort -> PSort
apply theta PI = PI
apply theta PO = PO
apply theta (PFun s t) =
  PFun (apply theta s) (apply theta t)
apply theta (PVar i) =
  case IntMap.lookup i (varSubst theta) of
    Nothing -> PVar i
    Just s -> s
apply theta (PSym i) =
  case HashMap.lookup i (symSubst theta) of
    Nothing -> PSym i
    Just s -> s

-- | Unify sorts without occur check.
unify :: PSort -> PSort -> RWS (HashMap.HashMap String PSort) () (SortSubst, Int) ()
unify s t
  | s == t = pure ()
unify (PFun s t) (PFun s' t') = do
  unify s s'
  unify t t'
unify (PSym i) s = do
  (theta, j) <- get
  case HashMap.lookup i (symSubst theta) of
    Nothing -> do
      let theta' = SortSubst (HashMap.singleton i s) mempty
      put (theta' <> theta, j)
    Just t ->
      unify t s
unify s (PSym i) =
  unify (PSym i) s
unify (PVar i) s = do
  (theta, j) <- get
  case IntMap.lookup i (varSubst theta) of
    Nothing -> do
      let theta' = SortSubst mempty (IntMap.singleton i s)
      put (theta' <> theta, j)
    Just t ->
      unify t s
unify s (PVar i) =
  unify (PVar i) s
unify _ _ = error "Sorts don't match!"

-- | Fresh unification variable.
fresh :: RWS (HashMap.HashMap String PSort) () (SortSubst, Int) PSort
fresh = do
  (subst, s) <- get
  put (subst, s + 1)
  pure (PVar s)