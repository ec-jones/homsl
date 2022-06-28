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
    fromFormula,
    fromFormulaList,
    toFormula,
  )
where

import Debug.Trace
import Data.Foldable hiding (null)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Hashable
import GHC.Generics
import HoMSL.Syntax
import Control.DeepSeq
import Prelude hiding (lookup, null)

-- | A collection of clauses grouped by head.
newtype ClauseSet = ClauseSet
  { getClauses :: HashMap.HashMap AtomType (HashSet.HashSet Formula)
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
insert :: AtomType -> Formula -> ClauseSet -> ClauseSet
insert head fm (ClauseSet cs) =
  ClauseSet (HashMap.alter (Just . HashSet.insert fm . fromMaybe HashSet.empty) head cs)

-- | Lookup formula with the given head.
-- N.B. Looking up a flat atom returns all /shallow clauses/.
lookup :: AtomType -> ClauseSet -> [Formula]
lookup (Flat p) (ClauseSet cs) = 
  HashMap.foldMapWithKey (\head clauses -> 
      case head of
        Shallow p' _
          | p == p' -> HashSet.toList clauses
        _ -> []
  ) cs
lookup head (ClauseSet cs) =
  case HashMap.lookup head cs of
    Nothing -> []
    Just ys -> HashSet.toList ys

-- | Create a clause set from a list of formulas.
fromFormulaList :: [Formula] -> ClauseSet
fromFormulaList = foldl' go mempty
  where
    go :: ClauseSet -> Formula -> ClauseSet
    go cs (Conj fs) = foldl' go cs fs
    go cs fm@((Atom (App (Sym p) (Apps (Sym f) _)))) =
      insert (Shallow p (Left f)) fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) (Apps (Sym f) _))) body) =
      insert (Shallow p (Left f)) fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) (Apps (Var x) _))) body) =
      insert (Shallow p (Right x)) fm cs
    go cs fm@(Atom (App (Sym p) (Apps (Var x) _))) =
      insert (Shallow p (Right x)) fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) _)) body) =
      insert (Flat p) fm cs
    go cs fm@(Atom (App (Sym p) _)) =
      insert (Flat p) fm cs
    go cs _ = error "Invalid clause head!"

-- | Create a clause set from a body.
fromFormula :: Formula -> ClauseSet
fromFormula fm = fromFormulaList [fm]

-- | Convert a clause set into a single formula.
toFormula :: ClauseSet -> Formula
toFormula (ClauseSet cs) = 
  Conj $ foldMap HashSet.toList cs