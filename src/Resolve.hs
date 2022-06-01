{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Resolve
  ( -- * Testing
    test,

    -- * Clause Sets
    ClauseSet,
    lookupClauses,
    toClauseSet,
    fromClauseSet,

    -- * Resolution
    saturate,
    resolve,
  )
where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import Data.Maybe
import Data.Traversable
import Debug.Trace
import Parser
import Syntax

-- * Testing

test :: ClauseSet
test =
  saturate $
    pProgram
      "forall (z : i -> i). P (F z) <= P (z G); \
      \ forall (g1 : i) (g2 : i). P (H g1 g2) <= Q g1 /\\ Q g2;\
      \ forall . Q G <= ; \
      \ forall . false <= P (F (H G)) "

-- * Clause Set

-- | A collection of automaton clauses groupped by head symbol.
newtype ClauseSet
  = ClauseSet
      ( HashMap.HashMap String (HashSet.HashSet Formula)
      )
  deriving stock (Show)

instance Semigroup ClauseSet where
  ClauseSet xs <> ClauseSet ys =
    ClauseSet (HashMap.unionWith HashSet.union xs ys)

instance Monoid ClauseSet where
  mempty = ClauseSet mempty

-- | Find all clauses in a given with head symbol.
lookupClauses :: String -> ClauseSet -> HashSet.HashSet Formula
lookupClauses x (ClauseSet clss) =
  HashMap.lookupDefault HashSet.empty x clss

-- | Create a clause set from a formula.
toClauseSet :: Formula -> Maybe ClauseSet
toClauseSet = go (ClauseSet HashMap.empty)
  where
    go :: ClauseSet -> Formula -> Maybe ClauseSet
    go (ClauseSet acc) head
      | Just p <- isAutoHead head =
          let hs = HashSet.singleton head
           in Just (ClauseSet $ HashMap.insertWith HashSet.union p hs acc)
    go acc (Conj ps) =
      foldM go acc ps
    go (ClauseSet acc) f@(Clause xs body head)
      | Just p <- isAutoHead head,
        isAutoBody body =
          let hs = HashSet.singleton f
           in Just (ClauseSet $ HashMap.insertWith HashSet.union p hs acc)
      | otherwise = Nothing
    go acc _ = Nothing

-- | Convert a clause set into a formula.
fromClauseSet :: ClauseSet -> Formula
fromClauseSet (ClauseSet clss) = Conj $ foldMap HashSet.toList clss

-- | Check if a term is a valid head returning the predicate.
isAutoHead :: Formula -> Maybe String
isAutoHead Ff = Just "false"
isAutoHead (Atom (App (Sym p) (Var _))) = Just p
isAutoHead (Atom (App (Sym p) (Apps (Sym f) xs)))
  | all (\case Var _ -> True; nonVar -> False) xs =
      Just p
isAutoHead (Atom (App (Sym p) (Apps (Var f) xs)))
  | all (\case Var _ -> True; nonVar -> False) xs =
      Just p
isAutoHead _ = Nothing

-- | Check if a formula is a valid body.
isAutoBody :: Formula -> Bool
isAutoBody Ff = False
isAutoBody (Atom (App (Sym _) (Var _))) = True
isAutoBody (Atom _) = False
isAutoBody (Conj ps) = all isAutoBody ps
isAutoBody cls@(Clause xs body (Atom head)) =
  isJust (toClauseSet cls)
    && isStrictAutoHead head
isAutoBody (Clause _ _ _) = False
isAutoBody (Exists _ _) = False

-- | Check if a formula is a valid head for a /nested/ automaton clause.
isStrictAutoHead :: Term -> Bool
isStrictAutoHead (App (Sym p) (Apps (Var f) xs)) =
  all (\case Var _ -> True; nonVar -> False) xs
    && not (null xs)
isStrictAutoHead _ = False

-- | Saturate a given set of formulas.
saturate :: [Formula] -> ClauseSet
saturate todo = runReader (go HashSet.empty [] todo) initEnv
  where
    go :: HashSet.HashSet Formula -> [Formula] -> [Formula] -> Reader ResolveEnv ClauseSet
    go seen paused todo = do
      case partitionMaybe toClauseSet todo of
        ([], gs) -> asks (\env -> foldl' (<>) (autoClauses env) gs)
        (f : fs, gs) ->
          local (\env -> env {autoClauses = foldl' (<>) (autoClauses env) gs}) $ do
            hs <- observeAllT (step f)
            if all (`HashSet.member` seen) hs
              then go seen (f : paused) fs
              else go (HashSet.fromList hs <> seen) [f] (paused ++ fs ++ hs)

    step :: Formula -> LogicT (Reader ResolveEnv) Formula
    step (Clause xs body head) = local
      ( \env -> env {resolveScope = mkScope xs <> resolveScope env}
      )
      $ do
        traceM ("\nClause: " ++ show (Clause xs body head))
        (body', subst) <- resolve body
        traceM
          ( "Step: "
              ++ show body
              ++ " ▷* "
              ++ show body'
          )
        -- assert (isNull subst)
        pure (Clause xs body' head)
    step _ = error "Non clause in input!"

partitionMaybe :: forall a b. (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = go
  where
    go :: [a] -> ([a], [b])
    go [] = ([], [])
    go (a : as) = case f a of
      Nothing -> first (a :) $ go as
      Just b -> second (b :) $ go as

-- | Perform resolution on a positive atom.

-- | The resolution environment.
data ResolveEnv = ResolveEnv
  { -- | Existing automaton clauses.
    autoClauses :: ClauseSet,
    -- | Existential variables.
    existentials :: Scope,
    -- | All local variables
    resolveScope :: Scope
  }

-- | Empty environment.
initEnv :: ResolveEnv
initEnv =
  ResolveEnv
    { autoClauses = mempty,
      existentials = mempty,
      resolveScope = mempty
    }

-- | Make a resolution step in a goal formul.a
resolve :: Formula -> LogicT (Reader ResolveEnv) (Formula, Subst)
resolve Ff = empty
resolve (Atom tm@(App (Sym p) arg)) = do
  env <- ask
  ( do
      -- (Assm)
      Apps (Var y) ss <- pure arg
      guard
        ( length ss > 0
            -- When existential we can use (ExInst)
            && not (y `inScope` existentials env)
        )

      -- Select a clause with an appropriate head
      choose (lookupClauses p (autoClauses env)) >>= \case
        Clause ys body (Atom head) -> do
          guard (length ys >= length ss)

          -- Delete irrelevant atoms from the body
          let (ys', xs) = List.splitAt (length ys - length ss) ys
              body' = restrictBody xs body
              head' = App (Sym p) (Apps (Var y) (fmap Var xs))
          guard (sortArgs (idSort y) == fmap idSort xs)

          pure
            ( Conj
                [ subst (mkSubst (zip xs ss)) body',
                  Clause xs body' (Atom head')
                ],
              mempty
            )
        nonClause -> empty
    )
    <|> do
      -- (ExInst) and (Step/Refl)
      -- Select a clause with an appropriate head
      choose (lookupClauses p (autoClauses env)) >>= \case
        Clause ys body (Atom head) -> do
          -- Match heads
          (thetaL, thetaR) <- (matchHead ys tm head)
          pure (subst thetaR body, thetaL)
        Atom head -> do
          -- Match heads
          (thetaL, thetaR) <- (matchHead [] tm head)
          pure (Conj [], thetaL)
        nonClause -> empty
resolve (Atom a) = error ("Atom is not well-typed!")
resolve (Conj fs) = do
  -- Select one conjunct to resolve.
  (fs', theta) <- resolveConj fs
  pure (Conj fs', theta)
resolve (Clause xs body head)
  | Atom t <- head, isStrictAutoHead t = empty
  | otherwise =
      case toClauseSet body of
        Nothing -> error "Non-automaton nested implication!"
        Just body' -> do
          -- Add local automaton clauses.
          local
            ( \env ->
                env
                  { autoClauses = autoClauses env <> body',
                    resolveScope = mkScope xs <> resolveScope env
                  }
            )
            $ do
              (head', theta) <- resolve head
              pure (Clause xs body head', theta)
resolve (Exists x body) =
  -- Add existential variable.
  local
    ( \env ->
        env
          { existentials = mkScope [x] <> existentials env,
            resolveScope = mkScope [x] <> resolveScope env
          }
    )
    $ do
      -- Resolve in body.
      (body', theta) <- resolve body
      case lookupSubst x theta of
        Nothing -> pure (Exists x body', theta)
        Just tm -> do
          -- Existentials only get instantiated by fresh existentials.
          pure
            ( foldl' (flip Exists) body' (listScope $ freeVars tm),
              removeFromSubst [x] theta
            )

-- Select one conjunct to resolve.
resolveConj ::
  [Formula] ->
  LogicT (Reader ResolveEnv) ([Formula], Subst)
resolveConj [] = empty
resolveConj (p : ps) =
  ( do
      (p', theta) <- resolve p
      let ps' = subst theta <$> ps
      pure (p' : ps', theta)
  )
    <|> ( do
            (ps', theta) <- resolveConj ps
            let p' = subst theta p
            pure (p' : ps', theta)
        )

-- | Remove irrelevant atoms from an /automaton/ clause.
restrictBody :: [Id] -> Formula -> Formula
restrictBody xs = Conj . go []
  where
    go :: [Formula] -> Formula -> [Formula]
    go acc f@(Atom tm)
      | all (`elem` xs) (listScope $ freeVars tm) = f : acc
      | otherwise = acc
    go acc (Conj fs) =
      foldl' go acc fs
    go acc f@(Clause ys body head)
      -- We assume the body only concerns ys.
      | all (`elem` (xs ++ ys)) (listScope $ freeVars head) = f : acc
      | otherwise = acc
    go acc _ =
      error "Non-automaton clause!"

-- | @matchHead ys lhs rhs@ finds instances @theta@ of @ys@ and @theta'@ such that
-- @subst theta lhs = subst theta' rhs@ and @subst theta' rhs@ is closed.
-- The rhs is assumed to be /shallow/ and /linear/.
matchHead :: [Id] -> Term -> Term -> LogicT (Reader ResolveEnv) (Subst, Subst)
matchHead ys lhs rhs = execStateT (go lhs rhs) mempty
  where
    go :: Term -> Term -> StateT (Subst, Subst) (LogicT (Reader ResolveEnv)) ()
    go (Var x) (Var y)
      | x == y, y `notElem` ys = pure ()
    go (Sym f) (Sym g)
      | f == g = pure ()
      | otherwise = empty
    go (App fun arg) (App fun' arg') = do
      -- Decomposition
      go fun fun'
      go arg arg'
    go t (Var y)
      | y `elem` ys =
          -- Because the rhs is linear this is the first time y has been bound.
          modify ((mempty, mkSubst [(y, t)]) <>)
    -- RHS can only be MSL
    go (Var x) t'@(Apps (Sym fun) args) = do
      env <- ask
      gets (lookupSubst x . fst) >>= \case
        Nothing
          | x `inScope` existentials env -> do
              -- Expand x with fresh arguments.
              let (_, xs) =
                    mapAccumL
                      uniqAway
                      (resolveScope env)
                      [Id "" (idSort arg) i | (Var arg, i) <- zip args [0 ..]]
                  t = Apps (Sym fun) (fmap Var xs)
              modify ((mkSubst [(x, t)], mempty) <>)
              go t t' -- Match arguments
          | otherwise -> empty
        Just t ->
          go t t'
    go _ _ = empty

-- | Non-deterministic selection.
choose :: (Alternative m, Foldable f) => f a -> m a
choose = foldl' (\k f -> k <|> pure f) empty