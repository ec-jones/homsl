module HoMSL.Rewrite
  ( saturate) where

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Writer
import Data.Foldable
import Control.Monad.ST
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import HoMSL.Syntax
import Debug.Trace

-- | Satuate a set of clauses.
saturate :: [Formula] -> HashSet.HashSet AClause
saturate = go HashMap.empty HashSet.empty
  where
    go :: HashMap.HashMap Formula (Maybe (Term Id)) -> HashSet.HashSet AClause -> [Formula] -> HashSet.HashSet AClause
    go seen autos [] = autos
    go seen autos (clause : clauses) =
      case formulaToClause clause of
        Nothing
          | clause `HashMap.member` seen -> go seen autos clauses
          | otherwise ->
            let (clauses', selected) = stepWith autos clause
             in go (HashMap.insert clause selected seen) autos (clauses' ++ clauses)
        Just auto
          | auto `HashSet.member` autos -> go seen autos clauses
          | otherwise ->
            -- Find, and resaturate, clauses that are relevant to the new automaton clause
            let relevant = [ clause | (clause, Just selected) <- HashMap.toList seen,
                                      relevantAtom selected auto ]
                reducts = concatMap (fst . stepWith (HashSet.singleton auto)) relevant
             in 
              go seen (HashSet.insert auto autos) (reducts ++ clauses)
    
    stepWith :: HashSet.HashSet AClause -> Formula -> ([Formula], Maybe (Term Id))
    stepWith autos clause =
      let (xs, head, body) = viewClause clause
          (reducts, First selected) = runWriter $ observeAllT (step autos xs body)
       in (Clause xs (Atom head) <$> reducts, selected)

-- | Make a single reduction step in a non-automaton body.
-- The function also emits the selected atom (if it could be resolved with new top-level clauses).
step :: 
  HashSet.HashSet AClause -> -- ^ Global automaton clauses
  [Id] -> -- ^ Subjects of the formula.
  Formula -> -- ^ Body of a clause.
  LogicT (Writer (First (Term Id))) Formula
step autos subjects fm =
  go (HashSet.fromList subjects) autos fm
  where
    go :: Scope -- ^ Variables in scope
        -> HashSet.HashSet AClause -- ^ Local and global automaton clauses
        -> Formula -- ^ Formula to rewrite
        -> LogicT (Writer (First (Term Id))) Formula
    go scope autos (Atom atom@(App (Sym p) arg@(Apps (Sym f) ss))) = do
      -- (Step)
      lift (tell (pure atom))
      
      AClause xs p' arg' body <- msum (pure <$> HashSet.toList autos)
      guard (p == p')

      inst <- match xs arg' arg
      pure (subst inst body)
    go scope autos (Atom atom@(App (Sym p) arg@(Var x)))
      | x `elem` subjects = empty
      | otherwise = do
        -- (Refl)
        AClause xs p' arg' body <- msum (pure <$> HashSet.toList autos)
        guard (p == p')

        inst <- match xs arg' arg
        pure (subst inst body)
    go scope autos (Atom atom@(App (Sym p) arg@(Apps (Var x) ss)))
      | x `elem` subjects = do
        -- (Assm)
        lift (tell (pure atom))

        AClause xs p' _ body <- msum (pure <$> HashSet.toList autos)
        guard (p == p')

        -- Drop partially applied variables.
        let ys = drop (length xs - length ss) xs
        guard (sortArgs (idSort x) == map idSort ys)

        -- Create fresh instance.
        let (_, ys') = uniqAways scope ys
            rho = mkRenaming (zip ys ys')

        -- Build reduct  
        let inst = mkSubst (zip ys' ss)
            body' = subst rho (restrictBody ys body)
            head' = App (Sym p) (Apps (Var x) (map Var ys'))

        pure (Conj [subst inst body', Clause ys' (Atom head') body'])
      | otherwise = do
        -- (Step)
        AClause xs p' arg' body <- msum (pure <$> HashSet.toList autos)
        guard (p == p')

        inst <- match xs arg' arg
        pure (subst inst body)
    go scope autos (Atom _) = error "Atom is not well-formed!"
    go scope autos (Conj []) = empty
    go scope autos (Conj (fm : fms)) =
      case formulaToNestedClauses subjects fm of
        Nothing -> do
          -- (AndL)
          fm' <- go scope autos fm
          pure (Conj (fm' : fms))
        Just _ -> do
          -- (AndR)
          fms' <- go scope autos (Conj fms)
          pure (Conj [fm, fms'])
    go scope autos (Exists _ _) = error "Existentials are not yet supported!"
    go scope autos (Clause xs head body)
      | all (`notElem` xs) (freeVars head) = do
        -- (Scope1)
        pure head
      | Atom (App (Sym p) arg@(Apps (Var x) ss)) <- head,
        x `elem` subjects = empty
      | otherwise = do
          -- (ImpImp)
          let (scope', xs') = uniqAways scope xs
              rho = mkRenaming (zip xs xs')
              body' = subst rho body
              
          -- Extend antecedent with local automaton clauses
          let Just autos' = formulaToNestedClauses xs' body'

          head' <- go scope' (autos' <> autos) (subst rho head)
          pure (Clause xs' head' body')

-- | Check if the atom could be resolved with the clause.
relevantAtom :: Term Id -> AClause -> Bool
relevantAtom (App (Sym p) (Apps (Sym f) _)) (AClause _ p' (Apps (Sym f') _) _) =
  p == p' && f == f'
relevantAtom (App (Sym p) (Apps (Var x) ss)) (AClause xs p' _ _) =
  p == p' && 
    let ys = drop (length xs - length ss) xs
     in sortArgs (idSort x) == map idSort ys
relevantAtom _ _ = False

-- -- | Reduce a formula to automaton form.
-- rewrite :: 
--   forall s.
--   Table s -> -- ^ Table of results
--   [Id] -> -- ^ Subjects of the formula.
--   Formula -> -- ^ Body of a clause.
--   Memo AClause s Formula
-- rewrite table subjects fm =
--   step (HashSet.fromList subjects) (\_ -> empty) fm
--   where
--     step :: Scope -- ^ Variables in scope
--         -> Table s -- ^ Local clauses
--         -> Formula -- ^ Formula to rewrite
--         -> Memo AClause s Formula 
--     step _ _ fm
--       | Just _ <- formulaToNestedClauses subjects fm = pure fm
--       | trace ("Step: " ++ show fm) False = undefined
--     step scope locals (Atom (App (Sym p) arg@(Apps (Sym f) ss))) = do
--       -- (Step)
--       AClause xs _ arg' body <- table p
--       inst <- match xs arg' arg
--       step scope locals (subst inst body)
--     step scope locals (Atom tm@(App (Sym p) arg@(Var x)))
--       | x `elem` subjects = pure (Atom tm)
--       | otherwise = do
--         -- (Refl)
--         AClause xs _ arg' body <- locals p
--         inst <- match xs arg' arg
--         step scope locals (subst inst body)
--     step scope locals (Atom (App (Sym p) arg@(Apps (Var x) ss)))
--       | x `elem` subjects = do
--         -- (Assm)
--         clause@(AClause xs _ _ body) <- locals p <|> table p

--         -- Drop partially applied variables.
--         let ys = drop (length xs - length ss) xs
--         guard (sortArgs x.sort == map (.sort) ys)

--         -- Create fresh instance.
--         let (_, ys') = uniqAways scope ys
--             rho = mkRenaming (zip ys ys')

--         -- Build reduct  
--         let inst = mkSubst (zip ys' ss)
--             body' = subst rho (restrictBody ys body)
--             head' = App (Sym p) (Apps (Var x) (map Var ys'))

--         body'' <- step scope locals (subst inst body')
--         pure (Conj [body'', Clause ys' (Atom head') body'])
--       | otherwise = do
--         -- (Step)
--         AClause xs _ arg' body <- locals p
--         inst <- match xs arg' arg
--         step scope locals (subst inst body)
--     step scope locals (Atom _) = error "Atom is not well-formed!"
--     step scope locals (Conj []) = pure (Conj [])
--     step scope locals (Conj (fm : fms)) = do
--       fm' <- step scope locals fm
--       fms' <- step scope locals (Conj fms)
--       pure (Conj [fm', fms'])
--     step scope locals (Exists _ _) = error "Existentials are not yet supported!"
--     step scope locals (Clause xs head body)
--       | all (`notElem` xs) (freeVars head) = do
--         -- (Scope1)
--         step scope locals head
--       | Atom (App (Sym p) arg@(Apps (Var x) ss)) <- head,
--         x `elem` subjects = do
--           -- Head is already of the right form.
--           pure (Clause xs head body)
--       | otherwise = do
--           -- (ImpImp)
--           let (scope', xs') = uniqAways scope xs
--               rho = mkRenaming (zip xs xs')
--               body' = subst rho body

--               -- Extend local clauses with clauses from the body.
--               locals' p = asum [ pure aclause | 
--                                       let Just clauses = formulaToNestedClauses xs' body',
--                                       aclause@(AClause _ p' (Apps (Var x') _) _) <- HashSet.toList clauses,
--                                       p == p'
--                                   ] <|> locals p

--           head' <- step scope' locals' (subst rho head)
--           if all (`notElem` xs') (freeVars head')
--             then pure head'
--             else empty -- step scope locals (Clause xs' head' body')

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