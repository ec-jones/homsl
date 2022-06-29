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

-- | Rewrite the body goal clauses, deriving automaton clauses in the process.
satisfiable :: ClauseSet.ClauseSet -> Bool
satisfiable clauses = runST $ mdo
  table <- memo $ \headShape -> do
    -- Select a clause with the given head.
    (xs, head, body) <- msum [pure (viewClause clause) | clause <- ClauseSet.lookup headShape clauses]
    traceM ("Rewriting: " ++ show (Clause xs (Atom head) body))

    -- Rewrite the body using the recursively constructed table.
    body' <-
      rewrite
        table
        Sequent
          { variables = IdEnv.fromList [(x, (x, False)) | x <- xs],
            consequent = body
          }
    pure (Clause xs (Atom head) body')

  null <$>
    runMemo (rewrite table Sequent { variables = mempty, 
          consequent = Atom (App (Sym "q0") (Sym "S")) })

-- | A sequent for rewriting.
data Sequent = Sequent
  { -- | Variables, marked as universally or existentially quantified.
    variables :: IdEnv.IdEnv (Id, Bool),
    -- | The goal formula in focus.
    consequent :: Formula
  }
  deriving stock (Show)

-- | Make any number of reduction steps.
rewrite ::
  forall s.
  (AtomType -> Memo Formula s Formula) ->
  Sequent ->
  Memo Formula s Formula
rewrite table sequent@Sequent {..} = do
  (consequent', subst) <- step table sequent

  -- There should be no existentials in the top-level.
  unless (IdEnv.null (substMap subst)) $
    error "Uncaught existential variable!"

  -- Something weird has happend here!
  unless (all (`IdEnv.member` variables) (freeVars consequent')) $
    error ("Unbound variable in reduct!" ++ show (consequent, consequent'))

  ( do
      guard (consequent /= consequent')
      rewrite table sequent {consequent = consequent'}
    )
    <|> pure consequent'

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
          let (_, ys) = List.splitAt (length xs - length ss) xs

          -- Ensure valid partial application, x -> p zs.
          guard
            ( length xs >= length ss
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
          pure (Conj [ subst inst body', Clause ys' (Atom head') body'], mempty)
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
        pure (Clause xs (subst inst body') body, mempty)
    Clause xs (Atom pxss@(App (Sym p) (Apps (Var x) ss))) body
      | not (isAutomatonBody xs body) -> error "Non automaton body!"
      | x `elem` xs -> do
          -- (Imp/Refl/Step)
          (ys, head, body') <- selectClause (ClauseSet.fromFormula body) (Shallow p (Right x))
          inst <- match ys head pxss

          traceM ("Selected5: " ++ show (Clause ys (Atom head) body'))
          pure (Clause xs (subst inst body') body, mempty)
      | all (`notElem` xs) (freeVars pxss) ->
          -- (Scope1)
          pure (Atom pxss, mempty)
      | all (`elem` map Var xs) ss ->
          pure (Clause xs (Atom pxss) body, mempty)
  where
    -- | Choose antecedent clause or a clause from the table.
    selectClause :: ClauseSet.ClauseSet -> AtomType -> Memo Formula s ([Id], Term Id, Formula)
    selectClause locals pattern =
      msum (pure . viewClause <$> ClauseSet.lookup pattern locals)
        <|> case pattern of
          Shallow _ (Right _) -> empty -- No global clause with variable head.
          nonLocal -> do
            (xs, head, body) <- viewClause <$> table pattern
            if isAutomatonBody xs body
              then do
                traceM ("Produce: " ++ show (Clause xs (Atom head) body))
                pure (xs, head, body)
              else empty -- Clause has not been sufficiently rewritten

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
  x `elem` xs &&
    (all (\s -> any (\y -> s == Var y) ys) ss) &&
      isAutomatonBody ys body
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
