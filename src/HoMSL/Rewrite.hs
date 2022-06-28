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

-- * Sequents

-- | A rewriting sequent with semantic hashing.
data Sequent = Sequent
  { -- | Collection of variables in scope, marked as existential.
    scope :: IdEnv.IdEnv (Id, Bool),
    -- | Local automaton clauses.
    antecedent :: ClauseSet.ClauseSet,
    -- | The focused goal being rewriten.
    consequent :: Formula,
    -- | Is the focus the head of a nested clause.
    nested :: Bool,
    -- | Partial solution to existential variables.
    solution :: Subst
  }
  deriving stock (Show)

instance Hashable Sequent where
  hashWithSalt s sequent =
    hashWithSalt s (sequent.nested, toFormula sequent, sequent.solution)

instance Eq Sequent where
  sequent1 == sequent2 =
    (sequent1.nested, toFormula sequent1, sequent1.solution)
      == (sequent2.nested, toFormula sequent2, sequent2.solution)

-- | Create the initial sequent from a formula.
fromFormula :: Formula -> Sequent
fromFormula fm = Sequent mempty mempty fm False mempty

-- | Convert a sequent into it's logical form.
toFormula :: Sequent -> Formula
toFormula Sequent {..} =
  let us = [u | (u, False) <- toList scope]
      es = [e | (e, True) <- toList scope]
      head = foldl' (flip Exists) consequent es
   in Clause us head (ClauseSet.toFormula antecedent)

-- * Rewriting

-- | Normalise a sequent to a valid body formula.
-- We assume the sequent is /canonical/.
rewrite :: ClauseSet.ClauseSet -> Formula -> [Formula]
rewrite prog body = runST $ mdo
  rewrite <- memo (step prog rewrite)
  fmap toFormula <$> 
    runMemo (step prog rewrite $ fromFormula body)

-- | Rewrite a sequent.
step :: forall s. ClauseSet.ClauseSet -> (Sequent -> Memo Sequent s Sequent) -> Sequent -> Memo Sequent s Sequent
step _ _ sequent
  | trace ("Goal: " ++ show sequent.consequent) False = undefined
step prog rewrite sequent@Sequent {..} = do
  case consequent of
    Atom px@(App (Sym p) (Var x))
      | Just (_, True) <- IdEnv.lookup x scope -> do
          -- (ExInst)
          (xs, head@(Apps f _), body) <- selectClause (Flat p)
          traceM ("Selected1: " ++ show (Clause xs (Atom head) body) ++ " for " ++ show (toFormula sequent))

          -- Create fresh instance
          let (_, xs') = uniqAways (fmap fst scope) xs
              rho = mkRenaming (zip xs xs')
              head' = subst rho head
              body' = subst rho body
              scope' =
                IdEnv.fromList [(x', (x', True)) | x' <- xs'] <> IdEnv.delete x scope

          rewrite
            sequent
              { scope = scope',
                consequent = body',
                solution = mkSubst [(x, Apps f (fmap Var xs'))]
              }
      | nested -> do
          -- (Refl)
          (_, _, _) <- selectClause (Shallow p (Right x))
          pure sequent {consequent = Conj []}
      | otherwise -> pure sequent 
    Atom pyss@(App (Sym p) (Apps (Var y) ss))
      | nested,
        all isVar ss -> pure sequent
      | otherwise -> do
          -- (Assm)
          (xs, head, body) <- selectClause (Flat p)
          traceM ("Selected2: " ++ show (Clause xs (Atom head) body) ++ " for " ++ show (toFormula sequent) )

          -- Split variables into those that are partially applied
          let (_, ys) = List.splitAt (length xs - length ss) xs

          -- Ensure valid partial application, y -> p ys.
          guard
            ( length xs >= length ss
                && sortArgs (idSort y) == fmap idSort ys
            )

          -- Create fresh instance with restricted variables.
          let (_, ys') = uniqAways (fmap fst scope) ys
              rho = mkRenaming (zip ys ys')
              body' = restrictBody ys' (subst rho body)

              -- Build formula.
              inst = mkSubst (zip ys' ss)
              head' = App (Sym p) (Apps (Var y) (map Var ys'))
              fm =
                Conj
                  [ subst inst body',
                    Clause ys' (Atom head') body'
                  ]

          rewrite sequent {consequent = fm}
    Atom pfs@(App (Sym p) (Apps (Sym f) ss)) -> do
      -- (Step)
      (xs, head, body) <- selectClause (Shallow p (Left f))
      traceM ("Selected3: " ++ show (Clause xs (Atom head) body) ++ " for " ++ show (toFormula sequent) )

      inst <- match xs head pfs
      rewrite sequent {consequent = subst inst body}
    Atom _ -> error "Invalid atom in sequent!"
    Conj [] -> pure sequent
    Conj (fm : fms) -> do
      -- (AndL)
      result <- step prog rewrite $ sequent {consequent = fm}
      result' <-
        step prog rewrite $
              sequent
                { consequent = Conj [subst result.solution fm | fm <- fms],
                  solution = result.solution
                }
      pure
        result'
          { consequent = Conj [result.consequent, result'.consequent]
          }
    Exists x subgoal -> do
      -- (Ex/ExInst)
      result <-
        step prog rewrite
          sequent
            { scope = IdEnv.insert x (x, True) scope,
              consequent = subgoal
            }

      when (x `IdEnv.member` freeVars subgoal) $
        error "Escaped existential!"
      pure
        result
          { solution = deleteSubst [x] result.solution
          }
    Clause xs head body -> do
      -- (Imp)
      result <-
        step prog rewrite
          sequent
            { scope = IdEnv.fromList [(x, (x, False)) | x <- xs] <> scope,
              consequent = head,
              antecedent = ClauseSet.fromFormula body <> antecedent,
              nested = True
            }

      -- (Scope1)
      let head' = result.consequent
      if any (`elem` xs) (freeVars head')
        then
          pure
            sequent
              { consequent = Clause xs head' body,
                solution = result.solution
              }
        else
          pure
            sequent
              { consequent = head',
                solution = result.solution
              }
  where
    selectClause :: AtomType -> Memo Sequent s ([Id], Term Id, Formula)
    selectClause head =
      msum (pure . viewClause <$> ClauseSet.lookup head antecedent) <|> do
          (xs, head, body) <- msum $ map (pure . viewClause) $ ClauseSet.lookup head prog
          !() <- traceM ("Working On: " ++ show (Clause xs (Atom head) body))
          result <-
            rewrite
              Sequent
                { scope = IdEnv.fromList [(x, (x, False)) | x <- xs],
                  antecedent = mempty,
                  consequent = body,
                  nested = False,
                  solution = mempty
                }
          traceM ("Produced: " ++ show (Clause xs (Atom head) result.consequent))
          pure (xs, head, result.consequent)

-- | @matchHead xs head tm@ finds instance of @head@ that matches @tm@ instantitates @xs@.
-- N.B. The head is assumed to be shallow and linear.
match ::
  [Id] ->
  Term Id ->
  Term Id ->
  Memo Sequent s Subst
match xs = go mempty
  where
    go :: Subst -> Term Id -> Term Id -> Memo Sequent s Subst
    go theta (Var x) t
      | x `elem` xs = pure (mkSubst [(x, t)] <> theta)
      | Var x == t = pure theta
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
    go acc f@(Clause ys head body)
      -- We assume the body only concerns ys.
      | all (`elem` (xs ++ ys)) (freeVars head) = f : acc
      | otherwise = acc
    go acc _ =
      error "Non-automaton clause!"
