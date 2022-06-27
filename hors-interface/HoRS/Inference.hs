{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

-- | HoRS sort inference.
module HoRS.Inference
  ( inferSorts,
  )
where

import Control.Monad.ST
import Control.Monad.State
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.IntMap as IntMap
import Data.STRef
import HoMSL.Syntax
import HoRS.Syntax

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
