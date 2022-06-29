{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoFieldSelectors #-}

module HoMSL.Rewrite where

import Control.Monad.Memoization
import Control.Monad.Reader
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Control.Monad.ST
import Data.Foldable
import Data.Hashable
import qualified Data.List as List
import Debug.Trace
import qualified HoMSL.ClauseSet as ClauseSet
import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax

-- | A sequent for rewriting.
data Sequent = Sequent  {
    -- | Collection of variables in scope, marked as existential.
    scope :: IdEnv.IdEnv (Id, Bool),
    -- | The goal formula in focus.
    consequent :: Formula
  }
  deriving stock Show

-- | Rewrite the body goal clauses, deriving automaton clauses in the process.
satisfiable :: ClauseSet.ClauseSet -> Bool
satisfiable clauses = runST $ mdo
  table <- memo $ \headShape -> do
    -- Select a clause with the given head.
    (xs, head, body) <- msum [pure (viewClause clause) | clause <- ClauseSet.lookup headShape clauses]
    traceM ("Rewriting: " ++ show (Clause xs (Atom head) body))

    -- Rewrite the body using the recursively constructed table.
    let scope = IdEnv.fromList [(x, (x, False)) | x <- xs]
        consequent = body
    (body', subst) <- rewrite table Sequent { .. }

    -- There should be no existentials in the top-level.
    unless (IdEnv.null (substMap subst)) $
      error "Uncaught existential variable!"

    pure (Clause xs (Atom head) body')

  null <$>
    runMemo (table (Shallow "q0" (Left "S")))

-- | Rewrite a formula with a given table.
rewrite ::
  forall s.
  (AtomType -> Memo Formula s Formula) ->
  Sequent -> Memo Formula s (Formula, Subst) 
rewrite _ sequent
  | trace ("Goal: " ++ show sequent.consequent) False = undefined
rewrite table sequent@Sequent { .. } = 
  case consequent of
    Atom pfs@(App (Sym p) (Apps (Sym f) ss)) -> do
      -- (Step)
      (xs, head, body) <- selectClause mempty (Shallow p (Left f))
      traceM ("Selected: " ++ show (Clause xs (Atom head) body))

      inst <- match xs head pfs
      rewrite table sequent {consequent = subst inst body}

    Atom px@(App (Sym p) (Var x))
      | Just (_, True) <- IdEnv.lookup x scope -> do
          -- (ExInst/Step)
          (xs, head@(Apps f _), body) <- selectClause mempty (Flat p)
          traceM ("Selected: " ++ show (Clause xs (Atom head) body))

          -- Create fresh instance
          let (_, xs') = uniqAways (fmap fst scope) xs
              rho = mkRenaming (zip xs xs')
              head' = subst rho head
              body' = subst rho body
              scope' =
                IdEnv.fromList [(x', (x', True)) | x' <- xs'] <> IdEnv.delete x scope

          (fm, theta) <- rewrite table sequent { scope = scope', consequent = body' }
          pure (fm, mkSubst [(x, Apps f (fmap Var xs'))] <> theta)

      | Just (_, False) <- IdEnv.lookup x scope -> 
          pure (consequent, mempty)

      | Nothing <- IdEnv.lookup x scope ->
          error "Variable not in scope!"

    Atom pyss@(App (Sym p) (Apps (Var x) ss))
      | not (null ss),
        Just (_, False) <- IdEnv.lookup x scope -> do
          -- (Assm)
          (xs, head, body) <- selectClause mempty (Flat p)
          traceM ("Selected: " ++ show (Clause xs (Atom head) body))

          -- Split variables into those that are partially applied
          let (_, ys) = List.splitAt (length xs - length ss) xs

          -- Ensure valid partial application, x -> p zs.
          guard
            ( length xs >= length ss
                && sortArgs (idSort x) == fmap idSort ys
            )

          -- Create fresh instance with restricted variables.
          let (_, ys') = uniqAways (fmap fst scope) ys
              rho = mkRenaming (zip ys ys')
              body' = restrictBody ys' (subst rho body)

              -- Build formula.
              inst = mkSubst (zip ys' ss)
              head' = App (Sym p) (Apps (Var x) (map Var ys'))
              fm = Conj [subst inst body', Clause ys' (Atom head') body']

          rewrite table sequent { consequent = fm } 

      | Just (_, True) <- IdEnv.lookup x scope  -> 
        error "Higher-order existentials are not yet supported!"
        
      | Nothing <- IdEnv.lookup x scope ->
          error "Variable not in scope!"

    Atom _ -> error "Invalid atom in sequent!"

    Conj [] -> pure (Conj [], mempty)
    Conj (fm : fms) -> do
      -- (AndL/R)
      (fm', theta) <- rewrite table sequent { consequent = fm }
      (fms', theta') <- rewrite table sequent { consequent = Conj (subst theta <$> fms) }
      pure (Conj [fm', fms'], theta <> theta')
    
    Exists x body -> do
      -- (Ex/ExInst)
      (body', theta) <-
        rewrite table
          sequent
            { scope = IdEnv.insert x (x, True) scope,
              consequent = body
            }

      pure (body', deleteSubst [x] theta)

    Clause xs (Atom pfs@(App (Sym p) (Apps (Sym f) ss))) body -> do
      -- (Imp/Step)
      (ys, head, body') <- selectClause (ClauseSet.fromFormula body) (Shallow p (Left f))
      traceM ("Selected: " ++ show (Clause ys (Atom head) body'))
      inst <- match ys head pfs
      rewrite table sequent {consequent = Clause xs (subst inst body') body}

    Clause xs (Atom pxss@(App (Sym p) (Apps (Var x) ss))) body
      | all (`notElem` xs) (freeVars pxss) ->
        -- (Scope1)
        pure (Atom pxss, mempty)

      | x `notElem` xs,
        all (`elem` map Var xs) ss,
        not (null ss) -> 
          -- Clause is already in the right form.
          pure (consequent, mempty)

      | otherwise -> do
        -- (Imp/Refl/Step)
        (ys, head, body') <- selectClause (ClauseSet.fromFormula body) (Shallow p (Right x))
        traceM ("Selected: " ++ show (Clause xs (Atom head) body))
        inst <- match ys head pxss
        rewrite table sequent {consequent = Clause xs (subst inst body') body}

    Clause _ _ _ -> error ("Unexpected clause head in body: " ++ show consequent)

  where
    -- | Choose antecedent clause or a clause from the table.
    selectClause :: ClauseSet.ClauseSet -> AtomType -> Memo Formula s ([Id], Term Id, Formula)
    selectClause body head =
      msum (pure . viewClause <$> ClauseSet.lookup head body) <|>
        case head of
          Shallow _ (Right _) -> empty
          nonLocal -> viewClause <$> table head

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
      | x `elem` xs =  pure (mkSubst [(x, t)] <> theta)
      | otherwise = empty
    go theta (Sym f) (Sym g)
      | f == g = pure theta
      | otherwise = empty
    go theta (App fun arg) (App fun' arg') = do
      -- Decomposition
      theta' <- go theta fun fun'
      go theta' arg arg'
    go _ _ _ = empty

-- | Remove irrelevant atoms from the body of automaton clause.
restrictBody :: [Id] -> Formula -> Formula
restrictBody xs = Conj . go []
  where
    go :: [Formula] -> Formula -> [Formula]
    go acc f@(Atom tm)
      | all (`elem` xs) (freeVars tm) = f : acc
      | otherwise = acc
    go acc (Conj fs) =
      foldl' go acc fs
    go acc f@(Clause ys (Atom (App (Sym p) (Apps (Var x) _))) body)
      | x `elem` xs = f : acc
      | otherwise = acc
    go acc body =
      error ("Non-automaton clause: " ++ show body)
