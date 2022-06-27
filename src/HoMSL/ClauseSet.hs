{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HoMSL.ClauseSet
  ( ClauseSet (..),
    insert,
    lookup,
    fromList,
  )
where

import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import HoMSL.Syntax
import Control.DeepSeq
import Prelude hiding (lookup)

-- | A collection of clauses grouped by head symbol.
newtype ClauseSet = ClauseSet
  { getMap :: HashMap.HashMap (String, Maybe String) (HashSet.HashSet Formula)
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

-- | Insert a value into a table.
insert :: String -> Maybe String -> Formula -> ClauseSet -> ClauseSet
insert p mf fm (ClauseSet cs) =
  ClauseSet (HashMap.alter (Just . HashSet.insert fm . fromMaybe HashSet.empty) (p, mf) cs)

-- | Lookup values from the table.
lookup :: String -> Maybe String -> ClauseSet -> [Formula]
lookup p mf (ClauseSet cs) =
  case HashMap.lookup (p, mf) cs of
    Nothing -> []
    Just ys -> HashSet.toList ys

-- | Create a clause set from a list of formulas.
fromList :: [Formula] -> ClauseSet
fromList = foldl' go mempty
  where
    go :: ClauseSet -> Formula -> ClauseSet
    go cs (Conj fs) = foldl' go cs fs
    go cs fm@(Clause xs Ff body) =
      insert "false" Nothing fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) (Apps (Sym f) _))) body) =
      insert p (Just f) fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) _)) body) =
      insert p Nothing fm cs
    go cs fm@(Clause _ _ _) = error "Invalid clause head!"
    go cs fm =
      go cs (Clause [] fm (Conj []))
