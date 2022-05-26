{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Binder
  ( -- * Scope & Variables.
    Scope,
    Var (Free),
    freshen,

    -- * Binders.
    Binder,
    pattern Binder,

    -- * Free Variables.
    FreeVars (freeVars),
  )
where

import Data.Foldable
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.List qualified as List
import Data.Traversable
import GHC.Generics

-- | A collection of free variables.
type Scope = HashSet.HashSet String

-- | A free or bound variable.
data Var
  = -- | A free variable
    Free {-# UNPACK #-} !String
  | -- | A locally bound variable
    Bound {-# UNPACK #-} !Int
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

-- | Local binder with cheap equality.
data Binder x
  = Binder_
      {-# UNPACK #-} ![String]
      {-# UNPACK #-} !x
      deriving stock Show

{-# COMPLETE Binder #-}

-- | FreeVars a free variable from a term.
pattern Binder ::
  (?scope :: Scope, FreeVars x) =>
  (?scope :: Scope) =>
  [String] ->
  x ->
  Binder x
pattern Binder xs t <-
  Binder_ (freshen' ?scope -> Scoped xs) (instantiate 0 xs -> t)
  where
    Binder xs t = Binder_ xs (capture 0 xs t)

instance Eq x => Eq (Binder x) where
  Binder_ _ k == Binder_ _ k' =
    k == k'

instance Hashable x => Hashable (Binder x) where
  hashWithSalt s (Binder_ _ xs) =
    hashWithSalt s xs

-- * Freshening variables into a scope.

-- | FreeVars a scope.
data Scoped a
  = (?scope :: Scope) =>
    Scoped {-# UNPACK #-} !a

-- | Ensure the locally bound variables are not captured.
freshen :: (?scope :: Scope) => [String] -> ((?scope :: Scope) => [String] -> k) -> k
freshen xs k =
  case freshen' ?scope xs of
    Scoped xs' -> k xs'

-- | Ensure the given variable is not in scope.
freshen' :: Scope -> [String] -> Scoped [String]
freshen' scope xs =
  let (scope', ys) = mapAccumL go scope xs
   in let ?scope = scope'
       in Scoped ys
  where
    go :: Scope -> String -> (Scope, String)
    go scope x
      | x `HashSet.member` scope =
          case find (\i -> not ((x ++ show i) `HashSet.member` scope)) [0 .. ] of
            Nothing -> error "Unreachable"
            Just (i :: Int) ->
              (HashSet.insert (x ++ show i) scope, x ++ show i)
      | otherwise =
          (HashSet.insert x scope, x)

-- * Free Variables

-- | Structure containing variables.
class FreeVars x where
  -- | Capture local free variables.
  capture :: Int -> [String] -> x -> x
  default capture ::
    (Generic x, GFreeVars (Rep x)) =>
    Int ->
    [String] ->
    x ->
    x
  capture i x (from -> t) = to (gcapture i x t)

  -- | Instantiate local variables with free variables.
  instantiate :: Int -> [String] -> x -> x
  default instantiate ::
    (Generic x, GFreeVars (Rep x)) =>
    Int ->
    [String] ->
    x ->
    x
  instantiate i x (from -> t) = to (ginstantiate i x t)

  -- | Collect the free variables.
  freeVars :: x -> [String]
  default freeVars ::
    (Generic x, GFreeVars (Rep x)) => x -> [String]
  freeVars (from -> t) = gfreeVars t

instance FreeVars Var where
  capture i xs (Bound j) = Bound j
  capture i xs (Free x) =
    case x `List.elemIndex` xs of
      Nothing -> Free x
      Just j -> Bound (i + j)

  instantiate i xs (Free y) = Free y
  instantiate i xs (Bound j)
    | i <= j,
      j < i + length xs =
        Free (xs !! (j - i))
    | otherwise = Bound j

  freeVars (Bound i) = []
  freeVars (Free x) = [x]

instance FreeVars x => FreeVars (Binder x) where
  capture i xs (Binder_ ys p) =
    Binder_ ys (capture (length ys + i) xs p)

  instantiate i xs (Binder_ ys p) =
    Binder_ ys (instantiate (length ys + i) xs p)

  freeVars (Binder_ _ p) = freeVars p

instance (FreeVars x, Hashable x) => FreeVars (HashSet.HashSet x) where
  capture i xs = HashSet.map (capture i xs)

  instantiate i xs = HashSet.map (instantiate i xs)

  freeVars = foldMap freeVars

instance
  {-# OVERLAPPABLE #-}
  (Functor f, Foldable f, FreeVars v) =>
  FreeVars (f v)
  where
  capture i xs = fmap (capture i xs)

  instantiate i xs = fmap (instantiate i xs)

  freeVars = foldMap freeVars

instance FreeVars String where
  capture i x y = y

  instantiate i xs y = y

  freeVars y = []

-- * Generic instances.

class GFreeVars x where
  gcapture :: Int -> [String] -> x a -> x a

  ginstantiate :: Int -> [String] -> x a -> x a

  gfreeVars :: x a -> [String]

instance GFreeVars f => GFreeVars (M1 i t f) where
  gcapture i x (M1 p) = M1 (gcapture i x p)

  ginstantiate i x (M1 p) = M1 (ginstantiate i x p)

  gfreeVars (M1 p) = gfreeVars p

instance GFreeVars V1 where
  gcapture i x v1 =
    case v1 of {}

  ginstantiate i x v1 =
    case v1 of {}

  gfreeVars v1 =
    case v1 of {}

instance GFreeVars U1 where
  gcapture i x U1 = U1

  ginstantiate i x U1 = U1

  gfreeVars U1 = []

instance (GFreeVars f, GFreeVars g) => GFreeVars (f :+: g) where
  gcapture i x (L1 f) = L1 (gcapture i x f)
  gcapture i x (R1 f) = R1 (gcapture i x f)

  ginstantiate i x (L1 f) = L1 (ginstantiate i x f)
  ginstantiate i x (R1 f) = R1 (ginstantiate i x f)

  gfreeVars (L1 f) = gfreeVars f
  gfreeVars (R1 f) = gfreeVars f

instance (GFreeVars f, GFreeVars g) => GFreeVars (f :*: g) where
  gcapture i x (f :*: g) = gcapture i x f :*: gcapture i x g

  ginstantiate i x (f :*: g) = ginstantiate i x f :*: ginstantiate i x g

  gfreeVars (f :*: g) = gfreeVars f <> gfreeVars g

instance FreeVars c => GFreeVars (K1 i c) where
  gcapture i x (K1 c) = K1 (capture i x c)

  ginstantiate i x (K1 c) = K1 (instantiate i x c)

  gfreeVars (K1 c) = freeVars c