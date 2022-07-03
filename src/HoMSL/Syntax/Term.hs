{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | The syntax and sorts of terms.
module HoMSL.Syntax.Term
  ( -- * Identifiers
    Id (..),

    -- * Sorts
    Sort (..),
    sortArgs,
    isPredicate,

    -- * Terms
    Term (..),
    pattern Apps,
    termHead,
    isMaybeVar,
  )
where

import Data.Foldable
import Data.Hashable
import GHC.Generics

-- * Identifiers

-- | An identifier
data Id = Id
  { -- | The original name.
    name :: !String,
    -- | The sort of the identifier
    sort :: !Sort,
    -- | A unique used to avoid capture.
    unique :: {-# UNPACK #-} !Int
  }

instance Eq Id where
  x == y =
    x.unique == y.unique

instance Ord Id where
  x <= y =
    x.unique <= y.unique

instance Hashable Id where
  hashWithSalt s x =
    hashWithSalt s x.unique

instance Show Id where
  showsPrec _ x =
    showString x.name . showString "_" . shows x.unique

-- * Sorts

-- | Simple types over trees and propositions.
data Sort
  = -- | Individuals (i.e. trees)
    I
  | -- | Proposition
    O
  | -- | Function arrow
    Sort :-> Sort
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

infixr 0 :->

-- | Collect the maximal list of arguments of a sort.
sortArgs :: Sort -> [Sort]
sortArgs I = []
sortArgs O = []
sortArgs (s :-> t) =
  s : sortArgs t

-- | Does the sort ultimately return a proposition?
isPredicate :: Sort -> Bool
isPredicate I = False
isPredicate O = True
isPredicate (s :-> t) =
  isPredicate t

-- * Terms

-- | Applicative terms.
data Term a
  = -- | Local variable.
    Var a
  | -- | Function symbol or program-level variable.
    Sym String
  | -- | Application.
    App (Term a) (Term a)
  deriving stock (Eq, Functor, Foldable, Traversable, Generic)
  deriving anyclass (Hashable)

instance Applicative Term where
  pure = Var

  Var f <*> tm = fmap f tm
  Sym f <*> tm = Sym f
  App fun arg <*> tm =
    App (fun <*> tm) (arg <*> tm)

instance Monad Term where
  Var x >>= k = k x
  Sym f >>= k = Sym f
  App fun arg >>= k =
    App (fun >>= k) (arg >>= k)

instance Show a => Show (Term a) where
  showsPrec _ (Var x) = shows x
  showsPrec _ (Sym s) = showString s
  showsPrec p (Apps fun args) =
    showParen (p > 10) $
      showsPrec 11 fun
        . foldl' (\k arg -> k . showString " " . showsPrec 11 arg) id args

{-# COMPLETE Apps #-}

-- | Terms in spinal form.
pattern Apps :: Term a -> [Term a] -> Term a
pattern Apps fun args <-
  (viewApps -> (fun, reverse -> args))
  where
    Apps fun args = foldl' App fun args

-- | Collect the arguments to a term (in reverse order).
viewApps :: Term a -> (Term a, [Term a])
viewApps (Var x) = (Var x, [])
viewApps (Sym f) = (Sym f, [])
viewApps (App fun arg) =
  let (fun', args) = viewApps fun
   in (fun', arg : args)

-- | The variable of function symbol at the head of the term.
termHead :: Term a -> Term a
termHead (Apps f _) = f

-- | Is the term just a variable.
isMaybeVar :: Term a -> Maybe a
isMaybeVar (Var x) = Just x
isMaybeVar _ = Nothing