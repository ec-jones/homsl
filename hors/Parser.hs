{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.ST
import Debug.Trace
import Data.Char
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.STRef
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

-- | Find the sorts of terminals and non-terminals from the HoRS problem.
runInfer :: ([Rule], [Transition]) -> HashMap.HashMap String Sort
runInfer (rules, trans) = runST $ do
  env <- execStateT (mapM_ inferRule rules) mempty
  mapM toSort env

-- | Infer sorts for a rule.
inferRule :: Rule -> StateT (HashMap.HashMap String (USort s)) (ST s) ()
inferRule (Rule f xs rhs) = do
  s <- lookupSort f

  -- Create fresh unification variables for the arguments.
  ss <- replicateM (length xs) (lift $ UVar <$> newSTRef Nothing)
  lift $ unify s (foldr UFun UI ss)
  
  -- Match rhs in local environment.
  env <- get
  put (HashMap.fromList (zip xs ss) <> env)
  matchTerm rhs UI
  put env

-- | Infer a term's sort.
inferTerm :: Term String -> StateT (HashMap.HashMap String (USort s)) (ST s) (USort s)
inferTerm (Var x) = lookupSort x
inferTerm (Sym f) = lookupSort f
inferTerm (App fun arg) = do
  s <- inferTerm fun
  case s of
    UFun t r -> do
      matchTerm arg t
      pure r
    _ -> do
      t <- inferTerm arg
      lift $ do
        r <- UVar <$> newSTRef Nothing
        unify s (UFun t r)
        pure r

-- | Attempt to match a term to a given sort.
matchTerm :: Term String -> USort s -> StateT (HashMap.HashMap String (USort s)) (ST s) ()
matchTerm (Var x) s = do
  t <- lookupSort x
  lift (unify t s)
matchTerm (Sym f) s = do
  t <- lookupSort f
  lift (unify t s)
matchTerm (App fun arg) s = do
  t <- inferTerm arg
  matchTerm fun (UFun t s)

-- | Find the sort of a symbol or variable.
lookupSort :: String -> StateT (HashMap.HashMap String (USort s)) (ST s) (USort s)
lookupSort x = do
  env <- get
  case HashMap.lookup x env of
    Nothing -> do
      i <- lift $ newSTRef Nothing
      modify (HashMap.insert x (UVar i))
      pure (UVar i)
    Just s -> pure s

-- | Partial sorts with unification variables.
data USort s
  = UI
  | UO
  | UFun (USort s) (USort s)
  | UVar (UVar s)
  deriving stock (Eq)

-- | Unification variables.
type UVar s =
  STRef s (Maybe (USort s))

-- | Default unsolved variables to individuals.
toSort :: USort s -> ST s Sort
toSort UI = pure I
toSort UO = pure O
toSort (UFun s t) =
  (:->) <$> toSort s <*> toSort t
toSort (UVar i) = 
  readSTRef i >>= \case
    Nothing -> pure I -- error "Unsolved sort variable!"
    Just s -> toSort s

-- | Unify two partial sorts.
unify :: USort s -> USort s -> ST s ()
unify UI UI = pure ()
unify UO UO = pure ()
unify (UFun s t) (UFun s' t') = do
  unify s s'
  unify t t'
unify (UVar x) (UVar y) = do
  (x', s) <- pathCompression x
  (y', t) <- pathCompression y
  if x' == y'
    then pure ()
    else 
      case (s, t) of
        (Nothing, _) -> writeSTRef x' (Just (UVar y'))
        (_, Nothing) -> writeSTRef y' (Just (UVar x'))
        (Just s', Just t') ->
          unify s' t'
unify (UVar x) s = do
  (x', t) <- pathCompression x
  case t of
    Nothing -> writeSTRef x' (Just s)
    Just t' -> unify t' s
unify s (UVar x) = unify (UVar x) s
unify _ _ = error "Failed to unify sorts!"

-- | Path compression.
pathCompression :: UVar s -> ST s (UVar s, Maybe (USort s))
pathCompression x =
  readSTRef x >>= \case
    Nothing -> pure (x, Nothing)
    Just (UVar z) -> do
      (w, s) <- pathCompression z
      writeSTRef x (Just (UVar w))
      pure (w, s)
    Just nonVar -> pure (x, Just nonVar)