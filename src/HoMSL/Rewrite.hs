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
  table <- memo $ \p -> table p <|> do
    -- Select a clause defining the given predicate.
    clause <- asum [ pure clause | clause <- clauses, 
                                  let (xs, head@(Apps (Sym p') _), body) = viewClause clause,
                                  p == p' ]
    traceM ("Rewriting: " ++ show clause)

    -- Rewrite a clause to automaton form.
    let (xs, head, body) = viewClause clause
    body' <- rewrite xs table body
    let clause' = Clause xs (Atom head) body'

    case formulaToClause clause' of
      Nothing -> 
        error ("Reduct is non-automaton: " ++ show clause')
      Just aclause ->
        pure aclause

  runMemo (table "q0")

-- | Table of clauses grouped by head symbol.
type Table f =
  String -> Memo AClause f AClause

-- | Rewrite atoms in the body of a clause to an automaton formula.
rewrite :: 
  forall f.
  [Id] -> -- ^ Subjects of the formula.
  Table f -> -- ^ Table of results
    Formula -> -- ^ Body of a clause.
      Memo AClause f Formula
rewrite subjects = go (HashSet.fromList subjects)
  where
    go :: Scope -> Table f -> Formula -> Memo AClause f Formula
    go _ _ fm
      | trace ("Step: " ++ show (subjects, fm)) False = undefined
    go scope table (Atom (App (Sym p) arg@(Apps (Sym f) ss))) = do
      -- (Step)
      clause@(AClause xs _ arg' body) <- table p
      inst <- match xs arg' arg
      traceM ("Resolve with: " ++ show (clauseToFormula clause))
      go scope table (subst inst body)
    go scope table (Atom (App (Sym p) arg@(Var x)))
      | x `elem` subjects = pure (Atom (App (Sym p) arg)) 
      | otherwise = do
        -- (Refl)
        clause@(AClause xs _ arg' body) <- table p
        inst <- match xs arg' arg
        traceM ("Resolve with: " ++ show (clauseToFormula clause))
        go scope table (subst inst body)
    go scope table (Atom (App (Sym p) arg@(Apps (Var x) ss)))
      | x `elem` subjects = do
        -- (Assm)
        clause@(AClause xs _ _ body) <- table p
        traceM ("Resolve with: " ++ show (clauseToFormula clause))

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
        go scope table (Conj [subst inst body', Clause ys' (Atom head') body'])
      | otherwise = do
        -- (Step)
        clause@(AClause xs _ arg' body) <- table p
        traceM ("Resolve with: " ++ show (clauseToFormula clause))
        inst <- match xs arg' arg
        go scope table (subst inst body) 
    go scope table (Atom _) = error "Atom is not well-formed!"
    go scope table (Conj []) = pure (Conj [])
    go scope table (Conj (fm : fms)) = do
      -- (AndL)
      fm' <- go scope table fm
      fms' <- go scope table (Conj fms)
      pure (Conj [fm', fms'])
    go scope table (Exists _ _) = error "Existentials are not yet supported!"
    go scope table (Clause xs head body)
      | all (`notElem` xs) (freeVars head) =
        -- (Scope1)
        go scope table head
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

              table' p = asum [ pure aclause | 
                                      let Just clauses = formulaToNestedClauses xs' body',
                                      aclause@(AClause _ p' _ _) <- HashSet.toList clauses,
                                      p == p'
                                  ] <|> table p

          head' <- go scope' table' (subst rho head)
          if all (`notElem` xs) (freeVars head')
            then pure head'
            else pure (Clause xs' head' body')

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