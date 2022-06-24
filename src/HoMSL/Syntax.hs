{-# LANGUAGE PatternSynonyms #-}

-- | The syntax of terms and formula.
module HoMSL.Syntax
  ( -- * Sorts
    Sort (..),
    sortArgs,
    isPredicate,

    -- * Identifiers
    Id (..),

    -- * Terms
    Term (..),
    pattern Apps,
    funSymbol,

    -- * Formulas
    Formula,
    pattern Ff,
    pattern Atom,
    pattern Conj,
    pattern Clause,
    pattern Exists,
    viewClause,

    -- * Scope
    IdEnv.Scope,
    IdEnv.mkScope,
    IdEnv.uniqAway,
    IdEnv.uniqAways,

    -- * Substitution
    IdEnv.Subst (..),
    IdEnv.mkSubst,
    IdEnv.mkRenaming,
    IdEnv.lookupSubst,
    IdEnv.deleteSubst,
    IdEnv.FreeVars (..),
  )
where

import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax.Formula
import HoMSL.Syntax.Term
