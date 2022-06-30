{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}

module HoMSL.Rewrite where

import Control.Monad.Memoization
import Control.Monad.Reader
import Control.Monad.ST
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable
import qualified Data.List as List
import Debug.Trace
import qualified HoMSL.ClauseSet as ClauseSet
import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax

-- * Sequents

-- | A sequent (i.e. body of a clause) for rewriting.
data Sequent = Sequent
  { -- | Variables, marked as universally or existentially quantified.
    variables :: IdEnv.IdEnv (Id, Bool),
    -- | The goal formula in focus.
    consequent :: Formula
  }
  deriving stock (Show)

instance Hashable Sequent where
  hashWithSalt s =
    hashWithSalt s . toFormula

instance Eq Sequent where
  seq1 == seq2 =
    toFormula seq1 == toFormula seq2

-- | Logical interpretation of a sequent.
toFormula :: Sequent -> Formula
toFormula Sequent {..} =
  let us = [x | (x, False) <- toList variables]
      es = [x | (x, True) <- toList variables]
   in Clause us (foldl' (flip Exists) consequent es) (Conj [])

-- * Rewriting

-- | Rewrite the body goal clauses, deriving automaton clauses in the process.
satisfiable :: ClauseSet.ClauseSet -> Bool
satisfiable clauses = runST $ mdo
  -- Table of partially rewritten clauses by head symbol.
  table <- memo $ \pattern -> do
    (xs, head, body) <- msum [pure (viewClause clause) | clause <- ClauseSet.lookup pattern clauses]
    traceM ("Rewriting: " ++ show (Clause xs (Atom head) body))

    let variables = IdEnv.fromList [(x, (x, False)) | x <- xs]
        consequent = body
    body' <- rewrite Sequent {..}
    pure (Clause xs (Atom head) body')

  -- Rewrite a sequent to be the body of an automaton clause.
  rewrite <- memo $ \sequent@Sequent {..} -> do
    (consequent', _) <- step table sequent

    if consequent == consequent'
      then pure consequent
      else rewrite sequent {consequent = consequent'}

  -- Rewrite initial goal.
  let variables = mempty
      consequent = Atom (App (Sym "q0") (Sym "S"))
  null <$> runMemo (rewrite Sequent {..})

-- | Make some reduction steps in goal formula with the given table.
step ::
  forall s.
  (AtomType -> Memo Formula s Formula) ->
  Sequent ->
  Memo Formula s (Formula, Subst)
step _ sequent
  | trace ("Goal: " ++ show sequent.consequent) False = undefined
step table sequent@Sequent {..} =
  case consequent of
    Atom pfs@(App (Sym p) (Apps (Sym f) ss)) -> do
      -- (Step)
      (xs, head, body) <- selectClause mempty (Shallow p (Left f))
      inst <- match xs head pfs

      traceM ("Selected1: " ++ show (Clause xs (Atom head) body))
      pure (subst inst body, mempty)
    Atom px@(App (Sym p) (Var x))
      | Just (_, True) <- IdEnv.lookup x variables -> do
          -- (ExInst/Step)
          (xs, head@(Apps f _), body) <- selectClause mempty (Flat p)
          traceM ("Selected2: " ++ show (Clause xs (Atom head) body))

          -- Create fresh instance
          let (_, xs') = uniqAways (fmap fst variables) xs
              rho = mkRenaming (zip xs xs')
              head' = subst rho head
              body' = subst rho body

          pure (body', mkSubst [(x, Apps f (fmap Var xs'))])
      | otherwise ->
          pure (consequent, mempty)
    Atom pyss@(App (Sym p) (Apps (Var x) ss))
      | Just (_, False) <- IdEnv.lookup x variables -> do
          -- (Assm)
          (xs, head, body) <- selectClause mempty (Flat p)

          -- Split variables into those that are partially applied
          let (zs, ys) = List.splitAt (length xs - length ss) xs

          -- Ensure valid partial application, x -> p zs.
          guard
            ( length ys == length ss
                && sortArgs (idSort x) == fmap idSort ys
            )

          -- Create fresh instance with restricted variables.
          let (_, ys') = uniqAways (fmap fst variables) ys
              rho = mkRenaming (zip ys ys')
              body' = restrictBody ys' (subst rho body)

              -- Build formula.
              inst = mkSubst (zip ys' ss)
              head' = App (Sym p) (Apps (Var x) (map Var ys'))

          traceM ("Selected3: " ++ show (Clause xs (Atom head) body))
          pure (Conj [subst inst body', Clause ys' (Atom head') body'], mempty)
    Atom _ -> error "Invalid atom in sequent!"
    Conj [] -> pure (Conj [], mempty)
    Conj (fm : fms) -> do
      -- (AndL)
      (fm', theta) <- step table sequent {consequent = fm}
      if fm /= fm'
        then pure (Conj (fm' : fmap (subst theta) fms), theta)
        else do
          -- (AndR)
          (fms', theta) <- step table sequent {consequent = Conj fms}
          pure (Conj [subst theta fm, fms'], theta)
    Exists x body -> do
      -- (ExInst)
      (body', theta) <-
        step
          table
          sequent
            { variables = IdEnv.insert x (x, True) variables,
              consequent = body
            }

      case lookupSubst x theta of
        Nothing -> pure (Exists x body', theta)
        Just tm -> do
          let xs = freeVars tm
          pure (foldl' (flip Exists) body' xs, deleteSubst [x] theta)
    Clause xs (Atom pfs@(App (Sym p) (Apps (Sym f) ss))) body
      | not (isAutomatonBody xs body) -> error "Non automaton body!"
      | otherwise -> do
          -- (Imp/Step)
          (ys, head, body') <- selectClause (ClauseSet.fromFormula body) (Shallow p (Left f))
          inst <- match ys head pfs
          traceM ("Selected4: " ++ show (Clause ys (Atom head) body'))

          let head' = subst inst body'
              xs' = filter (`IdEnv.member` freeVars head') xs
          pure (Clause xs' head' (restrictBody xs' body), mempty)
    Clause xs (Atom pxss@(App (Sym p) (Apps (Var x) ss))) body
      | not (isAutomatonBody xs body) -> error "Non automaton body!"
      | x `elem` xs -> do
          -- (Imp/Refl/Step)
          (ys, head, body') <- selectClause (ClauseSet.fromFormula body) (Shallow p (Right x))
          inst <- match ys head pxss
          traceM ("Selected5: " ++ show (Clause ys (Atom head) body'))

          let head' = subst inst body'
              xs' = filter (`IdEnv.member` freeVars head') xs
          pure (Clause xs' head' (restrictBody xs' body), mempty)
      | all (`notElem` xs) (freeVars pxss) ->
          -- (Scope1)
           pure (Atom pxss, mempty)
      | all (`elem` map Var xs) ss -> do
          let xs' = filter (`IdEnv.member` freeVars pxss) xs
          pure (Clause xs' (Atom pxss) (restrictBody xs' body), mempty)
      | otherwise ->
          -- Very suspicious!!
          empty
    _ -> 
      error ("Unexpected clause: " ++ show sequent)
  where
    -- | Choose antecedent clause or a clause from the table.
    selectClause :: ClauseSet.ClauseSet -> AtomType -> Memo Formula s ([Id], Term Id, Formula)
    selectClause locals pattern =
      msum (pure . viewClause <$> ClauseSet.lookup pattern locals)
        <|> case pattern of
          Shallow _ (Right _) -> empty -- No global clause with variable head.
          nonLocal -> do
            (xs, head, body) <- viewClause <$> table pattern
            guard (isAutomatonBody xs body)
            pure (xs, head, body)

-- | @matchHead xs head tm@ finds instance of @head@ that matches @tm@ instantitates @xs@.
-- N.B. The head is assumed to be shallow and linear.
match ::
  forall s.
  [Id] ->
  Term Id ->
  Term Id ->
  Memo Formula s Subst
match xs = go mempty
  where
    go :: Subst -> Term Id -> Term Id -> Memo Formula s Subst
    go theta (Var x) t
      | x `elem` xs = pure (mkSubst [(x, t)] <> theta)
      | Var y <- t,
        y == x =
          pure mempty
      | otherwise = empty
    go theta (Sym f) (Sym g)
      | f == g = pure theta
      | otherwise = empty
    go theta (App fun arg) (App fun' arg') = do
      -- Decomposition
      theta' <- go theta fun fun'
      go theta' arg arg'
    go _ _ _ = empty

-- | Check that the given formula is a valid automaton body.
isAutomatonBody :: [Id] -> Formula -> Bool
isAutomatonBody xs (Atom (App (Sym _) (Var x))) = x `elem` xs
isAutomatonBody xs (Conj fms) = all (isAutomatonBody xs) fms
isAutomatonBody xs (Clause ys (Atom (App (Sym p) (Apps (Var x) ss))) body) =
  x `elem` xs
    && (all (\s -> any (\y -> s == Var y) ys) ss)
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
