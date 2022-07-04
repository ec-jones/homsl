{-# LANGUAGE PatternSynonyms #-}

-- | The syntax of terms and formula.
module HoMSL.Syntax
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

    -- * Formulas,
    Formula,
    pattern Ff,
    pattern Atom,
    pattern Conj,
    pattern Exists,
    pattern Clause,
    viewClause,

    -- * Automaton Clauses
    AClause (..),
    clauseToFormula,
    clausesToFormula,
    formulaToClause,
    formulaToNestedClauses,

    -- * Scope
    Scope,
    uniqAway,
    uniqAways,

    -- * Substitutions
    Subst (substScope),
    mkSubst,
    mkRenaming,
    lookupSubst,
    extendSubst,

    -- * Substable
    Substable (..),
  )
where

import HoMSL.Syntax.Formula
import HoMSL.Syntax.Subst
import HoMSL.Syntax.Term
