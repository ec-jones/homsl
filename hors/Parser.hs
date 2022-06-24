{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module Parser where

import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.State
import Data.Char
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.STRef
import HoMSL.Rewrite
import HoMSL.Syntax
import Text.Parsec
import Text.Parsec.Token

-- TODO: Build clause set incrementally.
-- TODO: Accumulate states.
-- TODO: Split up into modules

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
horsToHoMSL :: String -> (Bool, ClauseSet)
horsToHoMSL str =
  case runReader (runParserT (pHoRS <* eof) () "" str) mempty of
    Left err -> error (show err)
    Right (rules, trans) ->
      let env = inferSorts (rules, trans)
          qs = HashMap.keys $ HashMap.filter isPredicate env
       in satisfiable $
            tableClauses
              ( mkGoal
                  : map (mkTransitionClause env) trans
                  ++ concatMap (mkRuleClauses qs env) rules
              )

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
inferSorts :: ([Rule], [Transition]) -> HashMap.HashMap String Sort
inferSorts (rules, trans) = runST $ do
  env <- execStateT (mapM_ inferRuleSort rules >> mapM_ inferTransSort trans) mempty
  mapM toSort env

-- | Infer sorts for a rule.
inferRuleSort :: Rule -> StateT (HashMap.HashMap String (USort s)) (ST s) ()
inferRuleSort (Rule f xs rhs) = do
  s <- lookupSort f

  -- Create fresh unification variables for the arguments.
  ss <- replicateM (length xs) (lift $ UVar <$> newSTRef Nothing)
  lift $ unify s (foldr UFun UI ss)

  -- Match rhs in local environment.
  modify (HashMap.fromList (zip xs ss) <>)
  matchTerm rhs UI
  modify (\env -> foldr HashMap.delete env xs)

-- | Infer sorts for a transition.
inferTransSort :: Transition -> StateT (HashMap.HashMap String (USort s)) (ST s) ()
inferTransSort (Transition q f rhs) = do
  s <- lookupSort q
  lift $ unify s (UFun UI UO)

  t <- lookupSort f
  go t (maybe 0 fst (IntMap.lookupMax rhs))
  where
    -- Unify sort with /minimum/ arity.
    go :: USort s -> Int -> StateT (HashMap.HashMap String (USort s)) (ST s) ()
    go UI n
      | n <= 0 = pure ()
      | otherwise = error "Arities don't match!"
    go UO _ = error "Unexpected higher-order predicate!"
    go (UFun s t) n = do
      lift $ unify s UI
      go t (n - 1)
    go (UVar i) n
      | n <= 0 = pure ()
      | otherwise = do
          j <- lift $ newSTRef Nothing
          lift $ unify (UVar i) (UFun UI (UVar j))
          go (UVar j) (n - 1)

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

-- | Find the sort of a symbol or variable or create a fresh unification variable if not present.
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
    else case (s, t) of
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

-- * Clause Construction

mkGoal :: Formula
mkGoal =
  Clause [] Ff (Atom (App (Sym "q0") (Sym "S")))

-- | Make a transition clause.
mkTransitionClause :: HashMap.HashMap String Sort -> Transition -> Formula
mkTransitionClause env (Transition q f rhs) =
  case HashMap.lookup f env of
    Nothing -> error "State not in scope!"
    Just s ->
      let xs = [Id "x" sArg i | (sArg, i) <- zip (sortArgs s) [1 ..]]
          head = Atom (App (Sym q) (Apps (Sym f) (map Var xs)))
          body =
            Conj
              [ Atom (App (Sym p) (Var (xs !! (i - 1))))
                | (i, p) <- IntMap.toList rhs
              ]
       in Clause xs head body

-- | Make clauses for each state and production rule.
mkRuleClauses :: [String] -> HashMap.HashMap String Sort -> Rule -> [Formula]
mkRuleClauses qs env (Rule f xs rhs) =
  case HashMap.lookup f env of
    Nothing -> error "State not in scope!"
    Just s -> do
      q <- qs -- A clause for each state
      -- xs <-> xs' could probably be made more efficient?
      let xs' = [Id x sArg i | (x, sArg, i) <- zip3 xs (sortArgs s) [1 ..]]
          rho x =
            case List.elemIndex x xs of
              Nothing -> error "Unbound variable in production rul!"
              Just i -> xs' !! i
          head = Atom (App (Sym q) (Apps (Sym f) (map Var xs')))
          body = Atom (App (Sym q) (fmap rho rhs))
      pure (Clause xs' head body)
