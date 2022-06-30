{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HoMSL.ClauseSet
  ( -- * Clause sets grouped by head.
    ClauseSet (..),
    null,
    insert,
    member,
    fromList,
    toList,

    -- * Queries
    Pattern (..),
    lookup,
    viewClause,
  )
where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Data.Foldable hiding (null, toList)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable
import qualified Data.List as List
import Data.Maybe
import GHC.Generics
import HoMSL.Syntax
import Prelude hiding (lookup, null)

-- | A collection of definite clauses grouped by predicate.
newtype ClauseSet = ClauseSet
  { getClauses :: HashMap.HashMap String (HashSet.HashSet Formula)
  }
  deriving newtype (NFData)

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
insert :: Formula -> ClauseSet -> ClauseSet
insert (Conj fs) cs = foldl' (flip insert) cs fs
insert fm@((Atom (App (Sym p) _))) (ClauseSet cs) =
  ClauseSet (HashMap.alter (Just . HashSet.insert fm . fromMaybe HashSet.empty) p cs)
insert fm@(Clause xs (Atom (App (Sym p) _)) body) (ClauseSet cs) =
  ClauseSet (HashMap.alter (Just . HashSet.insert fm . fromMaybe HashSet.empty) p cs)
insert _ _ = error "Formula is not a clause!"

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
member _ _ = error "Formula is not a clause!"

-- | Create a set of clause set from a list of formulas.
-- N.B. This function fails if any formula is not a (possibly degenerate) clause.
fromList :: [Formula] -> ClauseSet
fromList = foldl' (flip insert) mempty

-- | Enumerate clauses in a clause set.
toList :: ClauseSet -> [Formula]
toList (ClauseSet cs) = foldMap HashSet.toList cs

-- * Queries

-- | A condition placed upon clause heads.
data Pattern
  = Global String String
  | Local String Id
  | Assm String [Sort]
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

-- | Lookup formula with the given head.
lookup :: MonadPlus m => Pattern -> ClauseSet -> m Formula
lookup (Global p f) (ClauseSet cs) =
  case HashMap.lookup p cs of
    Nothing -> mzero
    Just clauses -> do
      clause <- msum [pure clause | clause <- HashSet.toList clauses]
      let (xs, head, body) = viewClause clause
      case head of
        App _ (Apps (Sym f') _)
          | f == f' -> pure clause
        nonX -> mzero
lookup (Local p x) (ClauseSet cs) =
  case HashMap.lookup p cs of
    Nothing -> mzero
    Just clauses -> do
      clause <- msum [pure clause | clause <- HashSet.toList clauses]
      let (xs, head, body) = viewClause clause
      case head of
        App _ (Apps (Var x') _)
          | x == x' -> pure clause
        nonX -> mzero
lookup (Assm p sortArgs) (ClauseSet cs) =
  case HashMap.lookup p cs of
    Nothing -> mzero
    Just clauses -> do
      clause <- msum [pure clause | clause <- HashSet.toList clauses]
      let (xs, head, body) = viewClause clause
          (_, ys) = List.splitAt (length xs - length sortArgs) xs
      guard (fmap idSort ys == sortArgs)
      pure clause

-- | View a formula as a clause.
viewClause :: Formula -> ([Id], Term Id, Formula)
viewClause (Atom tm) = ([], tm, Conj [])
viewClause (Clause xs (Atom tm) body) = (xs, tm, body)
viewClause nonClause = error ("Non-clause in clause set: " ++ show nonClause)
