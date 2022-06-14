{-# LANGUAGE PatternSynonyms #-}

-- | The syntax of terms and formula.
module HoMSL.Syntax
  ( -- * Identifiers
    Id (..),

    -- * Sorts
    Sort (..),
    sortArgs,

    -- * Terms
    Term (..),
    pattern Apps,

    -- * Formulas
    Formula,
    pattern Ff,
    pattern Atom,
    pattern Conj,
    pattern Clause,
    pattern Exists,
    pattern AClause,
    groupByHead,

    -- * Parsing
    parseProgram,

    -- * Scope
    IdEnv.Scope,
    IdEnv.mkScope,
    IdEnv.uniqAway,
    IdEnv.uniqAways,

    -- * Substitution
    IdEnv.Subst(..),
    IdEnv.mkSubst,
    IdEnv.mkRenaming,
    IdEnv.lookupSubst,
    IdEnv.deleteSubst,
    IdEnv.FreeVars (..),
  )
where

import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax.Formula
import HoMSL.Syntax.Parser
import HoMSL.Syntax.Term
