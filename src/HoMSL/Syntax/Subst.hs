-- | Scopes and substitutions.
module HoMSL.Syntax.Subst
  ( -- * Scope
    Scope,
    uniqAway,
    uniqAways,

    -- * Substitutions
    Subst (scope),
    mkSubst,
    mkRenaming,
    lookupSubst,
    extendSubst,

    -- * Substable
    Substable (..),
  )
where

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Traversable
import HoMSL.Syntax.Term

-- * Scopes

-- | A finite collection of identifiers.
type Scope = HashSet.HashSet Id

-- | Create a unique for an identifiers that is guaranteed to be disjoint from the given scope.
-- The resulting scope contains the identifier with the new unique.
uniqAway :: Scope -> Id -> (Scope, Id)
uniqAway scope x
  | x `HashSet.member` scope =
      let x' = x {unique = (maximum scope).unique + 1}
       in (HashSet.insert x' scope, x')
  | otherwise =
      (HashSet.insert x scope, x)

-- | Create fresh uniques for a list of identifiers.
uniqAways :: Scope -> [Id] -> (Scope, [Id])
uniqAways = mapAccumL uniqAway

-- * Substitutions

-- | A finite map from identifiers to terms.
data Subst = Subst
  { map :: HashMap.HashMap Id (Term Id),
    -- | The scope of resulting terms.
    scope :: Scope
  }

instance Show Subst where
  show theta =
    show theta.map

-- | N.B. Subst form a monoid under (left bias) /union/ not /composition/.
instance Semigroup Subst where
  theta1 <> theta2 =
    Subst
      { map = theta1.map <> theta2.map,
        scope = theta1.scope <> theta2.scope
      }

-- | N.B. Subst form a monoid under (left bias) /union/ not /composition/.
instance Monoid Subst where
  mempty = Subst mempty mempty

-- | Make a substitution.
mkSubst :: [(Id, Term Id)] -> Subst
mkSubst xts =
  Subst
    { map = HashMap.fromList xts,
      scope = foldMap (freeVars . snd) xts
    }

-- | Make a substitution that only maps variables to variables.
mkRenaming :: [(Id, Id)] -> Subst
mkRenaming xys =
  Subst
    { map = HashMap.fromList [(x, Var y) | (x, y) <- xys],
      scope = HashSet.fromList [y | (_, y) <- xys]
    }

-- | Lookup the value to which a variable is mapped.
lookupSubst :: Id -> Subst -> Maybe (Term Id)
lookupSubst x theta =
  HashMap.lookup x theta.map

-- | Extend a substitution with a mapping.
extendSubst :: Id -> Term Id -> Subst -> Subst
extendSubst x term theta = 
  Subst {
    map = HashMap.insert x term theta.map,
    scope = freeVars term <> theta.scope
  }

-- * Substable

-- | Structures that support substitution.
class Substable a where
  -- | Collect free variables.
  freeVars :: a -> Scope

  -- | Apply a substitution.
  subst :: Subst -> a -> a

instance Substable (Term Id) where
  freeVars :: Term Id -> Scope
  freeVars = foldMap HashSet.singleton

  subst :: Subst -> Term Id -> Term Id
  subst theta =
    ( >>=
        \x ->
          case HashMap.lookup x theta.map of
            Nothing -> Var x
            Just tm -> tm
    )

instance {-# OVERLAPPABLE #-} 
          (Foldable f, Functor f, Substable a) => Substable (f a) where
  freeVars :: f a -> Scope
  freeVars = foldMap freeVars

  subst :: Subst -> f a -> f a
  subst = fmap . subst