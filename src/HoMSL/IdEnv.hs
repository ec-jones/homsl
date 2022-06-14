{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HoMSL.IdEnv
  ( -- * Environment
    IdEnv,
    empty,
    fromList,
    null,
    lookup,
    member,
    insert,
    delete,
    deleteMany,

    -- * Scope
    Scope,
    mkScope,
    uniqAway,
    uniqAways,

    -- * Substitution
    Subst (..),
    mkSubst,
    mkRenaming,
    lookupSubst,
    deleteSubst,
    FreeVars (..),
  )
where

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Traversable
import HoMSL.Syntax.Term
import Prelude hiding (lookup, null)

-- * Environment

-- | Finite map from identifiers.
newtype IdEnv a
  = IdEnv (IntMap.IntMap a)
  deriving newtype (Functor, Foldable, Semigroup, Monoid)

-- | The empty environment.
empty :: IdEnv a
empty = IdEnv IntMap.empty

-- | Make an identifier environment.
fromList :: [(Id, a)] -> IdEnv a
fromList kvs =
  IdEnv (IntMap.fromList [(idUnique k, v) | (k, v) <- kvs])

-- | Is the environment empty?
null :: IdEnv a -> Bool
null (IdEnv env) =
  IntMap.null env

-- | Lookup the value associated with an identifier if present.
lookup :: Id -> IdEnv a -> Maybe a
lookup x (IdEnv env) =
  IntMap.lookup (idUnique x) env

-- | Check if the identifier is in the environment.
member :: Id -> IdEnv a -> Bool
member x (IdEnv env) =
  IntMap.member (idUnique x) env

-- | Extend an environment with an identifier.
insert :: Id -> a -> IdEnv a -> IdEnv a
insert k v (IdEnv env) =
  IdEnv (IntMap.insert (idUnique k) v env)

-- | Delete an identifier from an environment.
delete :: Id -> IdEnv a -> IdEnv a
delete x (IdEnv env) =
  IdEnv (IntMap.delete (idUnique x) env)

-- | Delete a list of identifier from an environment.
deleteMany :: [Id] -> IdEnv a -> IdEnv a
deleteMany xs (IdEnv env) =
  IdEnv (IntMap.withoutKeys env (IntSet.fromList (map idUnique xs)))

-- * Scope

-- | A finite set of identifiers in scope.
type Scope = IdEnv Id

-- | Make a scope from a list of variables.
mkScope :: [Id] -> Scope
mkScope xs = fromList (zip xs xs)

-- | Create a unique for an identifiers that is guaranteed to be disjoint from the given scope.
-- The resulting scope contains the identifier with the new unique.
uniqAway :: Scope -> Id -> (Scope, Id)
uniqAway scope@(IdEnv env) x
  | x `member` scope =
      let (unique, _) = IntMap.findMax env
          freshX = x {idUnique = unique + 1}
       in (insert freshX freshX scope, freshX)
  | otherwise =
      (insert x x scope, x)

-- | Create fresh uniques for a list of identifiers.
uniqAways :: Scope -> [Id] -> (Scope, [Id])
uniqAways = mapAccumL uniqAway

-- * Substitution

-- | A finite map from variables to terms.
data Subst = Subst {
  substMap :: IdEnv Term,
  substScope :: Scope
}

instance Semigroup Subst where
  theta <> theta' = Subst {
    substMap = substMap theta <> substMap theta',
    substScope = substScope theta <> substScope theta'
  }

instance Monoid Subst where
  mempty = Subst mempty mempty

-- | Make a substitution
mkSubst :: [(Id, Term)] -> Subst
mkSubst xts = 
  Subst {
    substMap = fromList [ (x, t) | (x, t) <- xts ],
    substScope = foldMap freeVars [ t | (_, t) <- xts ]
  }

-- | Make a renaming substitution.
-- Equivalent to `mkSubst [ (x, Var y) | (x, y) <- xys ]`
mkRenaming :: [(Id, Id)] -> Subst
mkRenaming xys =
  Subst {
    substMap = fromList [ (x, Var y) | (x, y) <- xys ],
    substScope = mkScope [ y | (_, y) <- xys ]
  }

-- | Lookup the value a variable is mapped to.
lookupSubst :: Id -> Subst -> Maybe Term
lookupSubst x = lookup x . substMap

-- | Remove a variable from a substitution
deleteSubst :: [Id] -> Subst -> Subst
deleteSubst xs subst =
  subst {
    substMap = deleteMany xs (substMap subst)
  }

-- | Structures that contain free variables and support substitution.
class FreeVars a where
  -- | Collect the free variables.
  freeVars :: a -> Scope

  -- | Apply a substitution.
  subst :: Subst -> a -> a

instance FreeVars Term where
  freeVars (Var x) = fromList [(x, x)]
  freeVars (Sym f) = mempty
  freeVars (App fun arg) =
    freeVars fun <> freeVars arg

  subst theta = go
    where
      go :: Term -> Term
      go (Var x) =
        case lookup x (substMap theta) of
          Nothing -> Var x
          Just t -> t
      go (Sym f) = Sym f
      go (App fun arg) =
        App (go fun) (go arg)
