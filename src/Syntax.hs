{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Syntax
  ( -- * Term
    Term,
    pattern Var,
    pattern Sym,
    pattern App,
    pattern Apps,

    -- * Formula
    Formula,
    pattern Ff,
    pattern Atom,
    pattern Conj,
    pattern Clause,
    pattern Exists,

    -- * Substitution
    Subst,
    Substable (..),
  )
where

import Binder
import Data.Foldable
import Data.HashMap.Lazy qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.List qualified as List
import GHC.Generics

-- * Terms

-- | Applicative terms with free variables.
data Term
  = -- | Program level predicates and function symbols.
    Sym {-# UNPACK #-} !String
  | -- | Local variables.
    Var_ {-# UNPACK #-} !Var
  | -- | Application.
    App Term Term
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FreeVars, Hashable)

-- instance Show Term where
--   showsPrec p (Var x) = showString x
--   showsPrec p (Sym f) = showString f
--   showsPrec p (App fun arg) =
--     showParen (p > 10) $
--       showsPrec 0 fun . showString " " . showsPrec 11 arg

{-# COMPLETE Var, Sym, App #-}

-- | A local variable.
pattern Var :: String -> Term
pattern Var x = Var_ (Free x)

{-# COMPLETE Apps #-}

-- | Inspect the head and spine of a term.
pattern Apps :: Term -> [Term] -> Term
pattern Apps fun args <-
  (viewApps -> (fun, args))
  where
    Apps fun args =
      foldl' App fun args

-- | Inspect the head and spine of a term.
viewApps :: Term -> (Term, [Term])
viewApps (App fun arg) =
  let (fun', args) = viewApps fun
   in (fun', arg : args)
viewApps t = (t, [])

-- * Formulas

-- | General Formulas in CNF.
-- Internally these are represented with de Bruijn inidicies for cheap comparison.
-- Variables are instantiated with locally fresh names upon pattern matching.
-- Note that *the constructors are not free* as they perform simplification.
data Formula
  = Ff
  | Atom
      Term
  | Conj_
      (HashSet.HashSet Formula)
  | Clause_
      (Binder (Formula :=> Formula))
  | Exists_
      (Binder Formula)
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable, FreeVars)

-- | An implication between formula.
data a :=> b
  = {-# UNPACK #-} !a
      :=> {-# UNPACK #-} !b
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable, FreeVars)

-- instance Show Formula where
--   showsPrec = let ?scope = HashSet.empty in showScoped
--     where
--       showScoped :: (?scope :: Scope) => Int -> Formula -> ShowS
--       showScoped p (Atom tm) = showsPrec p tm
--       showScoped p (Conj fs) =
--         showParen (p > 10) $ go fs
--         where
--           go [] = id
--           go [x] = showScoped p x
--           go (x : xs) =
--             showScoped p x . showString " /\\ " . go xs
--       showScoped p (Clause xs body head) =
--         showString "forall"
--           . foldl' (\k x -> k . showString " " . showString x) id xs
--           . showString ". "
--           . showScoped 0 body
--           . showString " => "
--           . showScoped 11 head
--       showScoped p (Exists x body) =
--         showString "exists " . showString x . showString ". " . showScoped 11 body

{-# COMPLETE Ff, Atom, Conj, Clause, Exists #-}

-- | A conjunction of formulas.
pattern Conj :: [Formula] -> Formula
pattern Conj ps <-
  Conj_ (HashSet.toList -> ps)
  where
    Conj = flattenConj HashSet.empty

-- | Eliminate nested conjunctions.
flattenConj :: HashSet.HashSet Formula -> [Formula] -> Formula
flattenConj ps []
  | [p] <- HashSet.toList ps = p
  | otherwise = Conj_ ps
flattenConj ps (Ff : rs) = Ff
flattenConj ps (Conj qs : rs) =
  flattenConj (ps `HashSet.union` HashSet.fromList qs) rs
flattenConj ps (r : rs) =
  flattenConj (HashSet.insert r ps) rs

-- | A universally quantified clause.
pattern Clause ::
  (?scope :: Scope) =>
  (?scope :: Scope) =>
  [String] ->
  Formula ->
  Formula ->
  Formula
pattern Clause xs body head <-
  (Clause_ (Binder xs (body :=> head)))
  where
    Clause xs Ff head = Conj []
    Clause xs body (Conj heads) =
      -- (ImpAnd)
      Conj [Clause xs body head | head <- heads]
    Clause xs body head
      | let ?scope = HashSet.union ?scope (HashSet.fromList xs),
        Clause ys body' head' <- head =
          -- (ImpImp)
          Clause (xs ++ ys) (Conj [body, body']) head'
    Clause xs body head =
      let xs' = (freeVars head `List.union` freeVars body) `List.intersect` xs
      in Clause_ (Binder xs' (body :=> head))

-- | An existential quantification.
pattern Exists ::
  (?scope :: Scope) =>
  (?scope :: Scope) =>
  String ->
  Formula ->
  Formula
pattern Exists x body <-
  Exists_ (Binder [x] body)
  where
    Exists x Ff = Ff
    Exists x (Conj ps)
      | null qs = Conj rs
      | not (null rs) =
          -- (Scope2)
          Conj (Exists x (Conj qs) : rs)
      where
        (qs, rs) = List.partition (elem x . freeVars) ps
    Exists x body
      | x `notElem` freeVars body = body
      | otherwise = Exists_ (Binder [x] body)

-- * Substitution

-- | A term substitution
type Subst = HashMap.HashMap String Term

-- | Structure that support substitution.
class Substable a where
  -- | The scope is require to contain all free variables in the substitution.
  subst :: (?scope :: Scope) => Subst -> a -> a

instance Substable Term where
  subst theta = go
    where
      go :: Term -> Term
      go (Var x) =
        case HashMap.lookup x theta of
          Nothing -> Var x
          Just t -> t
      go (Sym s) = Sym s
      go (App fun arg) =
        App (go fun) (go arg)

instance Substable Formula where
  subst theta = go
    where
      go :: (?scope :: Scope) => Formula -> Formula
      go Ff = Ff
      go (Atom a) =
        Atom (subst theta a)
      go (Conj fs) =
        Conj (go <$> fs)
      go (Clause xs body head) =
        Clause xs (go body) (go head)
      go (Exists x body) =
        Exists x (go body)