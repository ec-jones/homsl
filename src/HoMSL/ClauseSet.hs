{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HoMSL.ClauseSet
  ( -- * Clause sets grouped by head.
    ClauseSet (..),
    null,
    insert,
    lookup,
    member,
    partition,
    fromList,
    toList,
  )
where

import Debug.Trace
import Control.Applicative
import Data.Foldable hiding (null, toList)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Hashable
import GHC.Generics
import HoMSL.Syntax
import Control.DeepSeq
import Prelude hiding (lookup, null)

-- | A collection of definite clauses grouped by predicate.
newtype ClauseSet = ClauseSet
  { getClauses :: HashMap.HashMap String (HashSet.HashSet Formula)
  }
  deriving newtype NFData

instance Semigroup ClauseSet where
  ClauseSet cs <> ClauseSet cs' =
    ClauseSet (HashMap.unionWith HashSet.union cs cs')

instance Monoid ClauseSet where
  mempty = ClauseSet HashMap.empty

instance Show ClauseSet where
  show (ClauseSet cs) =
    unlines
      [ show x ++ " -> " ++ show y
        | (x, ys) <- HashMap.toList cs,
          y <- HashSet.toList ys
      ]

-- | Is the clause set empty.
null :: ClauseSet -> Bool
null (ClauseSet cs) =
  all HashSet.null cs

-- | Insert a formula into the clause set.
insert :: String -> Formula -> ClauseSet -> ClauseSet
insert p fm (ClauseSet cs) =
  ClauseSet (HashMap.alter (Just . HashSet.insert fm . fromMaybe HashSet.empty) p cs)

-- | Check if the formula appears in the clause set.
member :: Formula -> ClauseSet -> Bool
member fm@(Atom (App (Sym p) _)) (ClauseSet cs) =
  case HashMap.lookup p cs of
    Nothing -> False
    Just fms -> fm `HashSet.member` fms
member fm@(Clause _ (Atom (App (Sym p) _)) _) (ClauseSet cs) =
  case HashMap.lookup p cs of
    Nothing -> False
    Just fms -> fm `HashSet.member` fms

-- | Lookup formula with the given head.
lookup :: Alternative m =>  String -> ClauseSet -> m Formula
lookup p (ClauseSet cs) =
  case HashMap.lookup p cs of
    Nothing -> empty
    Just ys ->
      asum [ pure clause | clause <- HashSet.toList ys ]

-- | Partition a clause set according to a predicate.
partition :: (Formula -> Bool) -> ClauseSet -> (ClauseSet, ClauseSet)
partition p (ClauseSet cs) =
  (ClauseSet (HashSet.filter p <$> cs),
    ClauseSet (HashSet.filter p <$> cs))

-- | Create a set of clause set from a list of formulas.
-- N.B. This function fails if any formula is not a (possibly degenerate) clause.
fromList :: [Formula] -> ClauseSet
fromList = foldl' go mempty
  where
    go :: ClauseSet -> Formula -> ClauseSet
    go cs (Conj fs) = foldl' go cs fs
    go cs fm@((Atom (App (Sym p) _))) = insert p fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) _)) body) = insert p fm cs
    go cs _ = error "Formula is not a clause!"

-- | Enumerate clauses in a clause set.
toList :: ClauseSet -> [Formula]
toList (ClauseSet cs) = foldMap HashSet.toList cs