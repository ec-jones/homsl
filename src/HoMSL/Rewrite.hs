{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HoMSL.Rewrite where

import Control.Monad.Memoization
import Control.Monad
import Control.Monad.ST
import Control.Applicative
import Data.Foldable
import qualified Data.List as List
import Debug.Trace
import qualified HoMSL.ClauseSet as ClauseSet
import qualified Data.HashSet as HashSet
import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax

-- | Find all automaton clauses with a given head symbol.
saturateClauses :: ClauseSet.ClauseSet -> String -> [Formula]
saturateClauses prog p = runST $ mdo
  -- Table of automaton clauses.
  table <- memo $ \p -> do
    clause <- ClauseSet.lookup p prog
    rewrite clause

  -- Iteratively rewrite the body of a clause.
  rewrite <- memo $ \clause ->
    if isAutomaton clause
      then pure clause
      else do
        let (xs, head, body) = viewClause clause
        body' <- step table (mkScope xs) body
        rewrite (Clause xs (Atom head) body')

  runMemo (table p)

-- | Make at least one reduction step if possible.
step :: forall s. (String -> Memo Formula s Formula) -> Scope -> Formula -> Memo Formula s Formula
step table scope = fmap fst . go (mkScope [])
  where
    go :: Scope -> Formula -> Memo Formula s (Formula, Subst)
    go existentials (Atom tm@(App (Sym p) (Apps (Sym f) ss))) = do
      -- (Step)
      (xs, head, body) <- viewClause <$> table p
      inst <- match xs head tm
      go existentials (subst inst body)
    go existentials goal@(Atom (App (Sym p) (Var x)))
      | x `IdEnv.member` existentials = do
          -- (ExInst/Step)
          (xs, head@(Apps f _), body) <- viewClause <$> table p

          -- Create fresh instance
          let (_, xs') = uniqAways scope xs
              rho = mkRenaming (zip xs xs')

          -- Don't include fresh existentials to prevent cycles.
          (body', theta) <- go existentials (subst rho body)
          pure (body', mkSubst [(x, Apps f (fmap Var xs'))] <> theta)
      | otherwise = 
        pure (goal, mkSubst [])
    go existentials (Atom (App (Sym p) (Apps (Var x) ss)))
      | x `IdEnv.member` existentials =
          error "Higher-order existentials are not yet supported!"
      | otherwise = do
          -- (Assm)
          (xs, head, body) <- viewClause <$> table p

          -- Split variables into those that are partially applied
          let (zs, ys) = List.splitAt (length xs - length ss) xs

          -- Ensure valid partial application, x -> p zs.
          guard
            ( length ys == length ss
                && sortArgs (idSort x) == fmap idSort ys
            )

          -- Create fresh instance.
          let (_, ys') = uniqAways scope ys
              rho = mkRenaming (zip ys ys')

              -- Build formula.
              inst = mkSubst (zip ys' ss)
              body' = restrictBody ys' (subst rho body)
              head' = App (Sym p) (Apps (Var x) (map Var ys'))

          go existentials (Conj [subst inst body', Clause ys' (Atom head') body'])
    go existentials (Conj []) = pure (Conj [], mkSubst [])
    go existentials (Conj (fm : fms)) = do
      -- (AndL/R)
      (fm', theta) <- go existentials fm
      (fms', theta') <- go existentials (Conj (fmap (subst theta) fms))
      pure (Conj [fm', fms'], theta <> theta')
    go existentials (Exists x body) = do
      -- (ExInst)
      (body', theta) <- go (mkScope [x] <> existentials) body

      -- Capture fresh existentials.
      case lookupSubst x theta of
        Nothing -> pure (Exists x body', theta)
        Just tm -> do
          let xs = freeVars tm
          pure (foldl' (flip Exists) body' xs, deleteSubst [x] theta)
    go existentials (Clause xs (Atom tm@(App (Sym p) (Apps (Sym f) ss))) body) = do
      -- (Imp/Step)
      (ys, head, body') <- viewClause <$> table p
      inst <- match ys head tm

      go existentials (weaken $ Clause xs (subst inst body') body)
    go existentials goal@(Clause xs (Atom tm@(App (Sym p) (Apps (Var x) ss))) body)
      | x `IdEnv.member` existentials =
          error "Higher-order existentials are not yet supported!"
      | x `elem` xs = do
          -- (Imp/Refl/Step)
          (ys, head, body') <- viewClause <$> ClauseSet.lookup p (ClauseSet.fromList [body])
          inst <- match ys head tm

          go existentials (weaken $ Clause xs (subst inst body') body)
      | all (\s -> any (\x -> s == Var x) xs) ss =
          pure (goal, mkSubst [])
      | otherwise =
          -- (Assm)
          undefined
    go existentials goal =
      error ("Unexpected goal formula: " ++ show goal)

-- | @matchHead xs head tm@ finds instance of @head@ that matches @tm@ instantitates @xs@.
-- N.B. The head is assumed to be shallow and linear.
match :: forall m. MonadPlus m => [Id] -> Term Id -> Term Id -> m Subst
match xs = go (mkSubst [])
  where
    go :: Subst -> Term Id -> Term Id -> m Subst
    go theta (Var x) t
      | x `elem` xs = pure (mkSubst [(x, t)] <> theta)
      | Var y <- t,
        y == x =
          pure theta
      | otherwise = mzero
    go theta (Sym f) (Sym g)
      | f == g = pure theta
      | otherwise = mzero
    go theta (App fun arg) (App fun' arg') = do
      -- Decomposition
      theta' <- go theta fun fun'
      go theta' arg arg'
    go _ _ _ = mzero

-- | Check that the given formula is an automaton clause.
isAutomaton :: Formula -> Bool
isAutomaton (Atom (App (Sym p) (Sym f))) = True
isAutomaton (Atom _) = False
isAutomaton (Conj fs) =
  all isAutomaton fs
isAutomaton (Clause xs (Atom (App (Sym p) (Apps (Sym f) ss))) body) =
  -- We can assume the head is valid
  isAutomatonBody xs body
isAutomaton (Clause _ _ _) = False
isAutomaton (Exists _ _) = False

-- | Check that the given formula is a valid automaton body.
isAutomatonBody :: [Id] -> Formula -> Bool
isAutomatonBody xs (Atom (App (Sym _) (Var x))) = x `elem` xs
isAutomatonBody xs (Conj fms) = all (isAutomatonBody xs) fms
isAutomatonBody xs (Clause ys (Atom (App (Sym p) (Apps (Var x) ss))) body) =
  x `elem` xs
    && map Var xs == ss
    && isAutomatonBody ys body
isAutomatonBody _ _ = False

-- | Verify and restrict a formula to be the body of an automaton clause.
restrictBody :: [Id] -> Formula -> Formula
restrictBody xs = Conj . go []
  where
    go :: [Formula] -> Formula -> [Formula]
    go acc fm@(Atom (App (Sym _) (Var x)))
      | x `elem` xs = fm : acc
      | otherwise = acc
    go acc (Conj fms) =
      foldl' go acc fms
    go acc fm@(Clause ys (Atom (App (Sym p) (Apps (Var x) ss))) body)
      | x `elem` xs = fm : acc
      | otherwise = acc
    go acc body = error "Non-automaton!"

-- | Restrict clauses to only those variables in the head.
weaken :: Formula -> Formula
weaken (Clause xs head body) =
  let xs' = filter (`IdEnv.member` freeVars head) xs
   in Clause xs' head (restrictBody xs' body)
weaken (Conj fms) =
  Conj (fmap weaken fms)
weaken nonClause = nonClause
