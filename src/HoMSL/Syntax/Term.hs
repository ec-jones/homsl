{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Identifiers, Sorts, and Terms.
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
    funSymbol,
  )
where

import Data.Foldable

-- * Identifiers

-- | An identifier
data Id = Id
  { -- | The original name.
    idName :: !String,
    -- | The sort of the identifier
    idSort :: !Sort,
    -- | A unique used to avoid capture.
    idUnique :: {-# UNPACK #-} !Int
  }

instance Eq Id where
  x == y =
    idUnique x == idUnique y

instance Show Id where
  showsPrec _ x =
    showString (idName x) . showString "_" . shows (idUnique x)

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

-- | Does the sort ultimately return a proposition.
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
  deriving stock (Functor, Foldable, Traversable, Eq)

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
viewApps :: Term  a-> (Term a, [Term a])
viewApps (Var x) = (Var x, [])
viewApps (Sym f) = (Sym f, [])
viewApps (App fun arg) =
  let (fun', args) = viewApps fun
   in (fun', arg : args)

-- | Identify the function symbol (or prediate) at the head of a term.
funSymbol :: Term a -> Maybe String
funSymbol (Apps (Sym f) _) = Just f
funSymbol _ = Nothing