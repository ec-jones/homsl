{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Resolve
  ( test,
    ClauseSet,
    fromClauseSet,
    saturate,
    resolve,
  )
where

import Binder
import Control.Applicative
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.HashMap.Lazy qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List qualified as List
import Data.Maybe
import Data.Monoid
import Parser
import Syntax

-- * Testing

test :: ClauseSet
test =
  saturate $
    parseClauses
      "forall x1 x2. P x1 /\\ P x2 /\\ P G => P (F x1 x2); \
      \ P G; \
      \ exists z. P (z G) => false "

-- * Clause Set

-- | A collection of automaton clauses groupped by head symbol.
newtype ClauseSet
  = ClauseSet
      ( HashMap.HashMap String (HashSet.HashSet Formula)
      )

instance Semigroup ClauseSet where
  ClauseSet xs <> ClauseSet ys =
    ClauseSet (HashMap.unionWith HashSet.union xs ys)

instance Monoid ClauseSet where
  mempty = ClauseSet mempty

instance Show ClauseSet where
  show (ClauseSet xs) =
    unlines ((++ ";") <$> foldMap (fmap show . HashSet.toList) xs)

-- | Find all clauses in a given with head symbol.
lookupClauses :: String -> ClauseSet -> HashSet.HashSet Formula
lookupClauses x (ClauseSet clss) = 
  HashMap.lookupDefault HashSet.empty x clss

-- | Create a clause set from a formula.
toClauseSet :: (?scope :: Scope) => Formula -> Maybe ClauseSet
toClauseSet = go (ClauseSet HashMap.empty)
  where
    go :: (?scope :: Scope) => ClauseSet -> Formula -> Maybe ClauseSet
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
isAutoHead _ = Nothing

-- | Check if a formula is a valid body.
isAutoBody :: (?scope :: Scope) => Formula -> Bool
isAutoBody Ff = False
isAutoBody (Atom (App (Sym _) (Var _))) = True
isAutoBody (Atom _) = False
isAutoBody (Conj ps) = all isAutoBody ps
isAutoBody cls@(Clause xs body head) =
  isJust (toClauseSet cls)
isAutoBody (Exists _ _) = False

-- | Saturate a given set of formulas.
saturate :: [Formula] -> ClauseSet
saturate =
  let ?autoClauses = mempty
      ?scope = HashSet.empty
   in go
  where
    go ::
      (?scope :: Scope, ?autoClauses :: ClauseSet) =>
      [Formula] ->
      ClauseSet
    go fs =
      let (fs', autoClauses) = partitionMaybe toClauseSet fs
       in let ?autoClauses = foldl' (<>) ?autoClauses autoClauses
           in let res = concatMap step fs'
                  fs'' = HashSet.fromList (res ++ fs')
               in if fs'' == HashSet.fromList fs
                    then ?autoClauses
                    else go (HashSet.toList fs'')

    step ::
      (?scope :: Scope, ?autoClauses :: ClauseSet) =>
      Formula ->
      [Formula]
    step (Clause xs body head) = do
      body' <- resolve body
      pure (Clause xs body' head)
    step _ = error "Non clause in input!"

-- | Perform resolution on a positive atom.
resolve ::
  ( ?scope :: Scope,
    ?autoClauses :: ClauseSet
  ) =>
  Formula ->
  [Formula]
resolve =
  let ?exists = HashSet.empty
   in fmap fst . go
  where
    go ::
      (?scope :: Scope, ?autoClauses :: ClauseSet, ?exists :: Scope) =>
      Formula ->
      [(Formula, Subst)]
    go Ff = empty
    go (Atom tm@(App (Sym p) arg)) =
      ( do
          -- (Assm)
          Apps (Var y) ss <- pure arg
          guard
            ( length ss > 0
                -- Attempting to apply (Assm) with an existential variable diverges
                && not (y `HashSet.member` ?exists)
            )

          -- Select a clause with an appropriate head
          Clause ys body (Atom head) <- choose (lookupClauses p ?autoClauses)
          guard (length ys >= length ss)

          -- Delete irrelevant atoms from the body
          let (ys', xs) = List.splitAt (length ys - length ss) ys
          let body' = restrictBody xs body
              head = App (Sym p) (Apps (Var y) (fmap Var xs))

          pure
            ( Conj
                [ subst (HashMap.fromList (zip xs ss)) body',
                  Clause xs body' (Atom head)
                ],
              HashMap.empty
            )
      )
        <|> do
          -- (ExInst) and (Step/Refl)
          -- Select a clause with an appropriate head
          Clause ys body (Atom head) <- choose (lookupClauses p ?autoClauses)

          -- Match heads
          Just (thetaL, thetaR) <- pure (match tm head)
          pure (subst thetaR body, thetaL)
    go (Atom a) = error ("Atom is not well-typed! " ++ show a)
    go (Conj fs) = do
      (fs', theta) <- goConj fs
      pure (Conj fs', theta)
    go (Clause ys body head)
      | Just _ <- isAutoHead head = empty
      | otherwise =
          case toClauseSet body of
            Nothing -> error "Non-automaton nested implication!"
            Just body' -> do
              let -- ?heads = ?heads `HashSet.union` HashSet.fromList ys
                  ?autoClauses = ?autoClauses <> body'
              (head', theta) <- go head
              pure (Clause ys body head', theta)
    go (Exists x body) = do
      -- Add existential variable.
      let ?exists = HashSet.insert x ?exists

      -- Resolve in body.
      (body', theta) <- go body
      case HashMap.lookup x theta of
        Nothing ->
          pure (Exists x body', theta)
        Just tm ->
          -- Existentials only get instantiated by fresh existentials.
          pure
            ( foldl' (flip Exists) body' (freeVars tm),
              HashMap.delete x theta
            )

    --  | Apply a resolution to any of the conjuncts.
    goConj ::
      ( ?scope :: Scope,
        ?autoClauses :: ClauseSet,
        ?exists :: HashSet.HashSet String
      ) =>
      [Formula] ->
      [([Formula], Subst)]
    goConj [] = empty
    goConj (p : ps) =
      ( do
          (p', theta) <- go p
          let ps' = subst theta <$> ps
          pure (p' : ps', theta)
      )
        <|> ( do
                (ps', theta) <- goConj ps
                let p' = subst theta p
                pure (p' : ps', theta)
            )

-- | Remove irrelevant atoms from an /automaton/ clause.
restrictBody :: (?scope :: Scope) => [String] -> Formula -> Formula
restrictBody xs = Conj . go []
  where
    go :: (?scope :: Scope) => [Formula] -> Formula -> [Formula]
    go acc f@(Atom tm)
      | all (`elem` xs) (freeVars tm) = f : acc
      | otherwise = acc
    go acc (Conj fs) =
      foldl' go acc fs
    go acc f@(Clause ys body head)
      -- We assume the body only concerns ys.
      | all (`elem` (xs ++ ys)) (freeVars head) = f : acc
      | otherwise = acc
    go acc _ =
      error "Non-automaton clause!"

-- | @match xs lhs rhs@ finds instances @theta@ of @xs@ and @theta'@ such that
-- @subst theta lhs = subst theta' rhs@ and @subst theta' rhs@ is closed.
-- The rhs is assumed to be /shallow/ and /linear/.
match :: (?exists :: HashSet.HashSet String) => Term -> Term -> Maybe (Subst, Subst)
match lhs rhs = execStateT (go lhs rhs) mempty
  where
    go :: Term -> Term -> StateT (Subst, Subst) Maybe ()
    go (Var x) (Var y) | x == y = pure ()
    go (Sym x) (Sym y)
      | x == y = pure ()
      | otherwise = empty
    go (App fun arg) (App fun' arg') = do
      -- Decomposition
      go fun fun'
      go arg arg'
    go t (Var y) =
      -- Instantiate the j'th parameter of rhs with t.
      -- Because the rhs is linear this is the first time @j@ has been bound.
      modify (second (HashMap.insert y t))
    go (Var x) t'@(Apps fun args) =
      gets (HashMap.lookup x . fst) >>= \case
        Nothing
          | x `HashSet.member` ?exists -> do
              -- We use pseudo-free variables for the new existentials
              -- They needn't be instantiated as rhs is shallow.
              let t = Apps fun (Var . ("_" ++) . show <$> [0 .. length args - 1])
              modify (first (HashMap.insert x t))
              go t t'
          | otherwise -> empty
        Just t ->
          go t t'
    go _ _ = empty

-- * Combinators

choose :: (Foldable f, Alternative m) => f a -> m a
choose = getAlt . foldMap (Alt . pure)

partitionMaybe :: forall a b. (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = go
  where
    go :: [a] -> ([a], [b])
    go [] = ([], [])
    go (a : as) = case f a of
      Nothing -> first (a :) $ go as
      Just b -> second (b :) $ go as