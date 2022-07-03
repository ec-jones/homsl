{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}

module HoMSL.Rewrite
  ( saturate) where

import Control.Applicative
import Control.Monad.Memoization
import Control.Monad.RWS
import Data.Foldable
import Control.Monad.ST
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import HoMSL.Syntax
import Debug.Trace

saturate :: [Formula] -> HashSet.HashSet AClause
saturate clauses = runST $ mdo
  table <- memo $ \p -> do
    -- Select a clause defining the given predicate.
    clause <- asum [ pure clause | clause <- clauses, 
                                  let (xs, head@(App (Sym p') _), body) = viewClause clause,
                                  p == p'
                                  
                    ]

    -- Rewrite the clause to automaton form.
    let (xs, head, body) = viewClause clause
    body' <- rewrite table xs body
    let clause' = Clause xs (Atom head) body'
    case formulaToClause clause' of
      Nothing -> 
        error ("Reduce is not automaton: " ++ show clause')
      Just aclause ->
        pure aclause

  runMemo (table "q0")

-- | A table of clauses grouped by predicate.
type Table s =
  String -> Memo AClause s AClause

-- | Reduce a formula to automaton form.
rewrite :: 
  forall s.
  Table s -> -- ^ Table of results
  [Id] -> -- ^ Subjects of the formula.
  Formula -> -- ^ Body of a clause.
  Memo AClause s Formula
rewrite table subjects fm =
  go (HashSet.fromList subjects) (\_ -> empty) fm
  where
    go :: Scope -- ^ Variables in scope
        -> Table s -- ^ Local clauses
        -> Formula -- ^ Formula to rewrite
        -> Memo AClause s Formula 
    go scope locals (Atom (App (Sym p) arg@(Apps (Sym f) ss))) = do
      -- (Step)
      AClause xs _ arg' body <- table p
      inst <- match xs arg' arg
      go scope locals (subst inst body)
    go scope locals (Atom tm@(App (Sym p) arg@(Var x)))
      | x `elem` subjects = pure (Atom tm)
      | otherwise = do
        -- (Refl)
        AClause xs _ arg' body <- locals p
        inst <- match xs arg' arg
        go scope locals (subst inst body)
    go scope locals (Atom (App (Sym p) arg@(Apps (Var x) ss)))
      | x `elem` subjects = do
        -- (Assm)
        clause@(AClause xs _ _ body) <- locals p <|> table p

        -- Drop partially applied variables.
        let ys = drop (length xs - length ss) xs
        guard (sortArgs x.sort == map (.sort) ys)

        -- Create fresh instance.
        let (_, ys') = uniqAways scope ys
            rho = mkRenaming (zip ys ys')

        -- Build reduct  
        let inst = mkSubst (zip ys' ss)
            body' = subst rho (restrictBody ys body)
            head' = App (Sym p) (Apps (Var x) (map Var ys'))

        body'' <- go scope locals (subst inst body')
        pure (Conj [body'', Clause ys' (Atom head') body'])
      | otherwise = do
        -- (Step)
        AClause xs _ arg' body <- locals p
        inst <- match xs arg' arg
        go scope locals (subst inst body) 
    go scope locals (Atom _) = error "Atom is not well-formed!"
    go scope locals (Conj []) = pure (Conj [])
    go scope locals (Conj (fm : fms)) = do
      fm' <- go scope locals fm
      fms' <- go scope locals (Conj fms)
      pure (Conj [fm', fms'])
    go scope locals (Exists _ _) = error "Existentials are not yet supported!"
    go scope locals (Clause xs head body)
      | all (`notElem` xs) (freeVars head) = do
        -- (Scope1)
        go scope locals head
      | Atom (App (Sym p) arg@(Apps (Var x) ss)) <- head,
        x `elem` subjects,
        all (`elem` map Var xs) ss = do
          -- Head is already of the right form.
          pure (Clause xs head body)
      | otherwise = do
          -- (ImpImp)
          let (scope', xs') = uniqAways scope xs
              rho = mkRenaming (zip xs xs')
              body' = subst rho body

              -- Extend local clauses with clauses from the body.
              locals' p = asum [ pure aclause | 
                                      let Just clauses = formulaToNestedClauses xs' body',
                                      aclause@(AClause _ p' (Apps (Var x') _) _) <- HashSet.toList clauses,
                                      p == p'
                                  ] <|> locals p

          head' <- go scope' locals' (subst rho head)
          if all (`notElem` xs') (freeVars head')
            then pure head'
            else empty -- pure (Clause xs' head' body')

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