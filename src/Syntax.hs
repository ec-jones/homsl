{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Syntax
  ( -- * Identifiers
    Id (..),
    uniqAway,
    Scope,
    mkScope,
    inScope,
    lookupFromUnique,
    removeFromScope,
    listScope,

    -- * Sorts
    Sort (..),
    sortArgs,

    -- * Terms
    Term (..),
    pattern Apps,

    -- * Formulas
    Formula,

    -- ** Smart constructors
    pattern Ff,
    pattern Atom,
    pattern Conj,
    pattern Clause,
    pattern Exists,

    -- * Substitution
    Subst,
    Substable (..),
    mkSubst,
    mkRenaming,
    lookupSubst,
    removeFromSubst,
  )
where

import Data.Foldable
import qualified Data.HashSet as HashSet
import Data.Hashable
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Traversable

-- * Identifiers

-- | Identifier
data Id = Id
  { -- | The original name.
    idName :: {-# UNPACK #-} !String,
    -- | The identifier's sort.
    idSort :: {-# UNPACK #-} !Sort,
    -- | A unique used to avoid capture.
    idUnique :: {-# UNPACK #-} !Int
  }

instance Eq Id where
  x == y =
    idUnique x == idUnique y

instance Show Id where
  showsPrec _ x =
    showString (idName x) . showString "_" . showsPrec 0 (idUnique x)

-- | Create a unique for an identifiers that is guaranteed to be disjoint from the given scope.
-- The resulting scope contains the identifier with the new unique.
uniqAway :: Scope -> Id -> (Scope, Id)
uniqAway (Scope scope) x
  | idUnique x `IntMap.member` scope =
      let (u, _) = IntMap.findMax scope
          x' = x {idUnique = u + 1}
       in (Scope $ IntMap.insert (u + 1) x' scope, x')
  | otherwise =
      (Scope $ IntMap.insert (idUnique x) x scope, x)

-- | A collection of identifiers.
newtype Scope
  = Scope (IntMap.IntMap Id)
  deriving newtype (Show, Semigroup, Monoid)

-- | Create a scope from a list of identifiers.
mkScope :: [Id] -> Scope
mkScope xs = Scope $ IntMap.fromList [(idUnique x, x) | x <- xs]

-- | Check if an identifier is in scope.
inScope :: Id -> Scope -> Bool
inScope x (Scope scope) = IntMap.member (idUnique x) scope

-- | Find an identifier in scope from its unique.
lookupFromUnique :: Int -> Scope -> Maybe Id
lookupFromUnique u (Scope scope) = IntMap.lookup u scope

-- | Remove a list of identifiers from a scope.
removeFromScope :: [Id] -> Scope -> Scope
removeFromScope xs (Scope scope) =
  Scope (scope `IntMap.withoutKeys` IntSet.fromList [idUnique x | x <- xs])

-- | List the identifiers in scope.
listScope :: Scope -> [Id]
listScope (Scope scope) = IntMap.elems scope

-- * Sorts

-- | Simple types over trees and propositions.
data Sort
  = -- | Individuals (i.e. trees)
    I
  | -- | Proposition
    O
  | -- | Function arrow
    Sort :-> Sort
  deriving stock (Eq, Show)

infixr 0 :->

-- | Collect the maximal list of arguments of a sort.
sortArgs :: Sort -> [Sort]
sortArgs I = []
sortArgs O = []
sortArgs (s :-> t) =
  s : sortArgs t

-- * Terms

-- | Applicative terms.
data Term
  = -- | Local variable.
    Var Id
  | -- | Function symbol or program-level variable.
    Sym String
  | -- | Application.
    App Term Term
  deriving stock (Eq, Show)

-- | Terms in spinal form.
pattern Apps :: Term -> [Term] -> Term
pattern Apps fun args <-
  (viewApps -> (fun, reverse -> args))
  where
    Apps fun args = foldl' App fun args

-- | Collect the arguments to a term (in reverse order).
viewApps :: Term -> (Term, [Term])
viewApps (Var x) = (Var x, [])
viewApps (Sym f) = (Sym f, [])
viewApps (App fun arg) =
  let (fun', args) = viewApps fun
   in (fun', arg : args)

-- * Formulas

-- | General logical formulas.
data Formula = Formula
  { -- | The underlying shape of a formula.
    formulaShape :: FormulaShape,
    -- | The free variables in a formula.
    formulaFreeVars :: Scope,
    -- | Given de Buijn indicies hash the formula.
    formulaHash :: HashFun
  }

-- | The underlying shape of formula.
data FormulaShape
  = Ff_
  | Atom_ Term
  | Conj_ (HashSet.HashSet Formula)
  | Clause_ [Id] Formula Formula
  | Exists_ Id Formula
  deriving stock Show

instance Show Formula where
  show = show . formulaShape

-- | Equality and hashing check for alpha equivalence.
instance Eq Formula where
  (==) = eqAlpha (IntMap.empty, IntMap.empty)
    where
      eqAlpha :: (IntMap.IntMap Int, IntMap.IntMap Int) -> Formula -> Formula -> Bool
      eqAlpha env Ff Ff = True
      eqAlpha (envl, envr) (Atom t) (Atom s) = eqAlphaTm t s
        where
          eqAlphaTm :: Term -> Term -> Bool
          eqAlphaTm (Var x) (Var y)
            | Just i <- IntMap.lookup (idUnique x) envl,
              Just j <- IntMap.lookup (idUnique y) envr =
                i == j
            | Nothing <- IntMap.lookup (idUnique x) envl,
              Nothing <- IntMap.lookup (idUnique y) envr =
                x == y
            | otherwise = False
          eqAlphaTm (Sym f) (Sym g) = f == g
          eqAlphaTm (App fun arg) (App fun' arg') =
            eqAlphaTm fun fun' && eqAlphaTm arg arg'
          eqAlphaTm _ _ = False
      eqAlpha env (Conj fs) (Conj gs) =
        all (uncurry (eqAlpha env)) (zip fs gs)
      eqAlpha (envl, envr) (Clause xs body head) (Clause xs' body' head') =
        let envl' = shift xs envl
            envr' = shift xs' envr
         in eqAlpha (envl', envr') body body'
              && eqAlpha (envl', envr') head head'
      eqAlpha (envl, envr) (Exists x body) (Exists x' body') =
        let envl' = shift [x] envl
            envr' = shift [x'] envr
         in eqAlpha (envl', envr') body body'
      eqAlpha _ _ _ = False

-- | Equality and hashing check for alpha equivalence.
instance Hashable Formula where
  hashWithSalt s f =
    hashWithSalt s (formulaHash f IntMap.empty)

-- ** Smart constructors

{-# COMPLETE Ff, Atom, Conj, Clause, Exists #-}

-- | False.
pattern Ff :: Formula
pattern Ff <-
  Formula {formulaShape = Ff_}
  where
    Ff =
      Formula
        { formulaShape = Ff_,
          formulaFreeVars = mempty,
          formulaHash = hashFf
        }

-- | An atomic formula.
pattern Atom :: Term -> Formula
pattern Atom t <-
  Formula {formulaShape = Atom_ t}
  where
    Atom t =
      Formula
        { formulaShape = Atom_ t,
          formulaFreeVars = freeVars t,
          formulaHash = hashAtom (hashTerm t)
        }

-- | A conjunction of formulas.
pattern Conj :: [Formula] -> Formula
pattern Conj fs <-
  Formula {formulaShape = Conj_ (HashSet.toList -> fs)}
  where
    Conj = flattenConj mempty

-- | Eliminate nested conjunctions.
flattenConj :: (HashSet.HashSet Formula, Scope) -> [Formula] -> Formula
flattenConj (fs, fvs) []
  | [f] <- HashSet.toList fs = f
  | otherwise =
      Formula
        { formulaShape = Conj_ fs,
          formulaFreeVars = fvs,
          formulaHash = hashConj (formulaHash <$> HashSet.toList fs)
        }
flattenConj fs (Ff : _) = Ff
flattenConj (fs, fvs) (g@(Conj hs) : gs) =
  flattenConj
    ( fs `HashSet.union` HashSet.fromList hs,
      fvs <> freeVars g
    )
    gs
flattenConj (fs, fvs) (g : gs) =
  flattenConj
    ( HashSet.insert g fs,
      fvs <> freeVars g
    )
    gs

-- | A universally quantified clause.
pattern Clause :: [Id] -> Formula -> Formula -> Formula
pattern Clause xs body head <-
  Formula (Clause_ xs body head) _ _
  where
    Clause xs body (Conj heads) =
      -- (ImpAnd)
      Conj [Clause xs body head | head <- heads]
    Clause xs body (Clause ys body' head') =
      -- (ImpImp)
      let (_, ys') = mapAccumL uniqAway (mkScope xs) ys
          theta = mkRenaming (zip ys ys')
       in Clause (xs ++ ys') (Conj [body, subst theta body']) (subst theta head')
    Clause xs body head =
      Formula
        { formulaShape = Clause_ xs body head,
          formulaFreeVars = removeFromScope xs (freeVars body <> freeVars head),
          formulaHash = hashClause xs (formulaHash body) (formulaHash head)
        }

-- | An existential quantification.
pattern Exists :: Id -> Formula -> Formula
pattern Exists x body <-
  Formula (Exists_ x body) _ _
  where
    Exists x (Conj fs)
      | null gs = Conj hs
      | otherwise =
          -- (Scope2)
          Conj (Exists x (Conj gs) : hs)
      where
        (gs, hs) = List.partition (inScope x . freeVars) fs
    Exists x body
      | x `inScope` freeVars body =
          Formula
            { formulaShape = Exists_ x body,
              formulaFreeVars = removeFromScope [x] (freeVars body),
              formulaHash = hashExists x (formulaHash body)
            }
      | otherwise = body

-- * Substitution

-- | A finite map from identifiers to terms.
data Subst = Subst
  { -- | The underlying map.
    substMap :: IntMap.IntMap Term,
    -- | Free variables in the introduced term.
    substFreeVars :: Scope
  }
  deriving stock Show

instance Semigroup Subst where
  theta <> theta' =
    Subst
      { substMap = substMap theta <> substMap theta',
        substFreeVars = substFreeVars theta <> substFreeVars theta'
      }

instance Monoid Subst where
  mempty = Subst mempty mempty

-- | Create a substitution from a list of pairs.
mkSubst :: [(Id, Term)] -> Subst
mkSubst xts =
  Subst
    { substMap = IntMap.fromList [(idUnique x, t) | (x, t) <- xts],
      substFreeVars = foldMap (\(_, t) -> freeVars t) xts
    }

-- | Create a renaming substitution
mkRenaming :: [(Id, Id)] -> Subst
mkRenaming xys =
  Subst
    { substMap = IntMap.fromList [(idUnique x, Var y) | (x, y) <- xys],
      substFreeVars = foldMap (\(_, y) -> mkScope [y]) xys
    }

-- | Lookup the term assocaited with an identifier by a substitution.
lookupSubst :: Id -> Subst -> Maybe Term
lookupSubst x subst =
  IntMap.lookup (idUnique x) (substMap subst)

-- | Remove a list of identifiers from a substitution.
removeFromSubst :: [Id] -> Subst -> Subst
removeFromSubst xs subst =
  Subst
    { substMap = substMap subst `IntMap.withoutKeys` IntSet.fromList [idUnique x | x <- xs],
      substFreeVars = substFreeVars subst -- Conservatively retain all free variables.
    }

-- | Structures that support substitution.
class Substable a where
  -- | Collect the free variables.
  freeVars :: a -> Scope

  -- | Apply a substitution.
  subst :: Subst -> a -> a

instance Substable Term where
  freeVars (Var x) = mkScope [x]
  freeVars (Sym f) = mempty
  freeVars (App fun arg) =
    freeVars fun <> freeVars arg

  subst theta (Var x) =
    case lookupSubst x theta of
      Nothing -> Var x
      Just t -> t
  subst theta (Sym f) = Sym f
  subst theta (App fun arg) =
    App (subst theta fun) (subst theta arg)

instance Substable Formula where
  freeVars = formulaFreeVars

  subst theta Ff = Ff
  subst theta (Atom t) = Atom (subst theta t)
  subst theta (Conj fs) =
    Conj (subst theta <$> fs)
  subst theta (Clause xs body head) =
    let (_, xs') = mapAccumL uniqAway (substFreeVars theta <> freeVars body <> freeVars head) xs
        theta' = mkRenaming (zip xs xs') <> theta
     in Clause xs' (subst theta' body) (subst theta' head)
  subst theta (Exists x body) =
    let (_, x') = uniqAway (substFreeVars theta <> freeVars body) x
        theta' = mkRenaming [(x, x')] <> theta
     in Exists x' (subst theta' body)

-- * Hash Combinators

-- | Hash a value given a map that associates identifiers with their de Buijn index.
type HashFun = IntMap.IntMap Int -> Int

-- | Extend a de Buijn environment binding a list of identifiers.
shift :: [Id] -> IntMap.IntMap Int -> IntMap.IntMap Int
shift xs env =
  foldl'
    (\env' (x, i) -> IntMap.insert (idUnique x) i env')
    (fmap (+ length xs) env)
    (zip xs [0 ..])

hashTerm :: Term -> HashFun
hashTerm (Var x) env =
  case IntMap.lookup (idUnique x) env of
    Nothing -> hash ("Free", idUnique x)
    Just i -> hash ("Bound", i)
hashTerm (Sym f) env = hash ("Sym", f)
hashTerm (App fun arg) env =
  hash ("App", hashTerm fun env, hashTerm arg env)

hashFf :: HashFun
hashFf _ = hash "Ff"

hashAtom :: HashFun -> HashFun
hashAtom t env =
  hash ("Atom", t env)

hashConj :: [HashFun] -> HashFun
hashConj fs env =
  hash ("Conj", fmap ($ env) fs)

hashClause :: [Id] -> HashFun -> HashFun -> HashFun
hashClause xs head body env =
  let env' = shift xs env
   in hash ("Clause", head env', body env')

hashExists :: Id -> HashFun -> HashFun
hashExists x body env =
  let env' = shift [x] env
   in hash ("Exists", body env')