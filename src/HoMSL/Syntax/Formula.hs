{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Logical formulas.
module HoMSL.Syntax.Formula
  ( -- * Formulas,
    Formula,
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
  )
where

import Control.Applicative
import Control.Monad
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable
import qualified Data.List as List
import HoMSL.Syntax.Subst
import HoMSL.Syntax.Term

-- * Formulas

-- | General logical formulas.
data Formula = Formula
  { -- | The underlying shape of a formula.
    shape :: FormulaShape,
    -- | The free variables in a formula.
    freeVars :: Scope,
    -- | Given de Buijn indicies hash the formula.
    hash :: HashFun
  }

-- | The underlying shape of formula.
data FormulaShape
  = Atom_ (Term Id)
  | Conj_ (HashSet.HashSet Formula)
  | Clause_ [Id] Formula Formula
  | Exists_ Id Formula

-- | Equality and hashing check for alpha equivalence.
instance Eq Formula where
  (==) = eqAlpha (HashMap.empty, HashMap.empty)
    where
      eqAlpha :: (HashMap.HashMap Id Int, HashMap.HashMap Id Int) -> Formula -> Formula -> Bool
      eqAlpha (envl, envr) (Atom t) (Atom s) = eqAlphaTm t s
        where
          eqAlphaTm :: Term Id -> Term Id -> Bool
          eqAlphaTm (Var x) (Var y)
            | Just i <- HashMap.lookup x envl,
              Just j <- HashMap.lookup y envr =
                i == j
            | Nothing <- HashMap.lookup x envl,
              Nothing <- HashMap.lookup y envr =
                x == y
            | otherwise = False
          eqAlphaTm (Sym f) (Sym g) = f == g
          eqAlphaTm (App fun arg) (App fun' arg') =
            eqAlphaTm fun fun' && eqAlphaTm arg arg'
          eqAlphaTm _ _ = False
      eqAlpha env (Conj fs) (Conj gs) =
        length fs == length gs
          && all (uncurry (eqAlpha env)) (zip fs gs)
      eqAlpha (envl, envr) (Clause xs head body) (Clause xs' head' body') =
        let envl' = shift xs envl
            envr' = shift xs' envr
         in eqAlpha (envl', envr') head head'
              && eqAlpha (envl', envr') body body'
      eqAlpha (envl, envr) (Exists x body) (Exists x' body') =
        let envl' = shift [x] envl
            envr' = shift [x'] envr
         in eqAlpha (envl', envr') body body'
      eqAlpha _ _ _ = False

-- | Equality and hashing check for alpha equivalence.
instance Hashable Formula where
  hashWithSalt s f =
    hashWithSalt s (f.hash HashMap.empty)

instance Show Formula where
  showsPrec p (Atom t) = showsPrec p t
  showsPrec p (Conj fs) = showParen (p > 3) (showConj fs)
    where
      showConj :: [Formula] -> ShowS
      showConj [] = id
      showConj [f] = showsPrec 3 f
      showConj (f : fs) =
        showsPrec 3 f . showString " /\\ " . showConj fs
  showsPrec p (Clause xs head body) =
    showParen (p > 1) (showForall xs . showsPrec 2 head . showBody body)
    where
      showForall :: [Id] -> ShowS
      showForall [] = id
      showForall xs =
        showString "forall "
          . foldl' (\k x -> k . shows x . showString " ") id xs
          . showString "\b. "

      showBody :: Formula -> ShowS
      showBody (Conj []) = id
      showBody f = showString " <= " . showsPrec 2 f
  showsPrec p (Exists x body) =
    showParen (p > 1) (showString "exists " . shows x . showString ". " . showsPrec 2 body)

instance Substable Formula where
  freeVars fm = fm.freeVars

  subst theta (Atom t) =
    Atom (subst theta t)
  subst theta (Conj fs) =
    Conj (subst theta <$> fs)
  subst theta f@(Exists x body) =
    let (_, x') = uniqAway (theta.scope <> freeVars f) x
        theta' = mkRenaming [(x, x')] <> theta
     in Exists x' (subst theta' body)
  subst theta f@(Clause xs head body) =
    let (_, xs') = uniqAways (theta.scope <> freeVars f) xs
        theta' = mkRenaming (zip xs xs') <> theta
     in Clause xs' (subst theta' head) (subst theta' body)

-- * Smart constructors

{-# COMPLETE Atom, Conj, Exists, Clause #-}

-- | An atomic formula.
pattern Atom :: Term Id -> Formula
pattern Atom t <-
  Formula {shape = Atom_ t}
  where
    Atom t =
      Formula
        { shape = Atom_ t,
          freeVars = freeVars t,
          hash = hashAtom (hashTerm t)
        }

-- | A conjunction of formulas.
pattern Conj :: [Formula] -> Formula
pattern Conj fs <-
  Formula {shape = Conj_ (HashSet.toList -> fs)}
  where
    Conj = flattenConj mempty

-- | Eliminate nested conjunctions.
flattenConj :: (HashSet.HashSet Formula, Scope) -> [Formula] -> Formula
flattenConj (fs, fvs) []
  | [f] <- HashSet.toList fs = f
  | otherwise =
      Formula
        { shape = Conj_ fs,
          freeVars = fvs,
          hash = hashConj [f.hash | f <- HashSet.toList fs]
        }
flattenConj (fs, fvs) (g@(Conj hs) : gs) =
  flattenConj
    ( fs <> HashSet.fromList hs,
      fvs <> freeVars g
    )
    gs
flattenConj (fs, fvs) (g : gs) =
  flattenConj
    ( HashSet.insert g fs,
      fvs <> freeVars g
    )
    gs

-- | An existential quantification.
pattern Exists :: Id -> Formula -> Formula
pattern Exists x body <-
  Formula (Exists_ x body) _ _
  where
    Exists x (Conj fs)
      | null gs = Conj hs
      | otherwise =
          -- (Scope2)
          Conj (Exists x (Conj gs) : hs)
      where
        (gs, hs) = List.partition (HashSet.member x . freeVars) fs
    Exists x body
      | x `HashSet.member` freeVars body =
          Formula
            { shape = Exists_ x body,
              freeVars = HashSet.delete x (freeVars body),
              hash = hashExists x body.hash
            }
      | otherwise = body

-- | A universally quantified clause.
pattern Clause :: [Id] -> Formula -> Formula -> Formula
pattern Clause xs head body <-
  Formula (Clause_ xs head body) _ _
  where
    Clause [] head (Conj []) = head
    Clause xs (Conj heads) body =
      -- (ImpAnd)
      Conj [Clause xs head body | head <- heads]
    Clause xs head body =
      Formula
        { shape = Clause_ xs head body,
          freeVars =
            (freeVars body <> freeVars head)
              `HashSet.difference` HashSet.fromList xs,
          hash = hashClause xs head.hash body.hash
        }

-- | View a formula as a (non-automaton) definite clause.
viewClause :: Formula -> ([Id], Term Id, Formula)
viewClause (Atom tm) = ([], tm, Conj [])
viewClause (Clause xs (Atom tm) body) = (xs, tm, body)
viewClause _ = error "Formula is not a clause!"

-- * Automaton Clause

-- | Explicit representation of an automaton clause.
data AClause
  = AClause [Id] String (Term Id) Formula

instance Eq AClause where
  clause1 == clause2 =
    clauseToFormula clause1 == clauseToFormula clause2

instance Hashable AClause where
  hashWithSalt s =
    hashWithSalt s . clauseToFormula

instance Show AClause where
  show = show . clauseToFormula

-- | The logical interpretation of an automaton clause.
clauseToFormula :: AClause -> Formula
clauseToFormula (AClause xs p arg body) =
  Clause xs (Atom (App (Sym p) arg)) body

-- | Interpret a (conjunctive) set of clauses as a single formula.
clausesToFormula :: HashSet.HashSet AClause -> Formula
clausesToFormula clauses =
  Conj [clauseToFormula clause | clause <- HashSet.toList clauses]

-- | View a formula as a /top-levl/ automaton clause.
formulaToClause :: Formula -> Maybe AClause
formulaToClause (Atom (App (Sym p) (Sym f))) =
  Just (AClause [] p (Sym f) (Conj []))
formulaToClause (Clause xs (Atom (App (Sym p) arg@(Apps (Sym f) args))) body) = do
  _ <- formulaToNestedClauses xs body
  pure (AClause xs p arg body)
formulaToClause _ = Nothing

-- | View a formula as a conjunction of nested automaton clauses.
-- The first argument is the possible subjects.
formulaToNestedClauses :: [Id] -> Formula -> Maybe (HashSet.HashSet AClause)
formulaToNestedClauses xs = go HashSet.empty
  where
    go :: HashSet.HashSet AClause -> Formula -> Maybe (HashSet.HashSet AClause)
    go acc (Atom (App (Sym p) (Var x)))
      | x `elem` xs =
        pure (HashSet.insert (AClause [] p (Var x) (Conj [])) acc)
      | otherwise =
        empty
    go acc (Conj fms) =
      foldM go acc fms
    go acc (Clause ys (Atom (App (Sym p) arg@(Apps (Var x) args))) body)
      | x `elem` xs = do
          ys' <- mapM isMaybeVar args
          guard (all (`elem` ys) ys')
          _ <- formulaToNestedClauses ys' body
          pure (HashSet.insert (AClause ys' p arg body) acc)
      | otherwise = empty
    go _ _ = empty

-- -- The first argument are the possible local variable subjects.
-- -- If, and only if, there are no subjects may the clause must be top-level.
-- formulaToClauses :: [Id] -> Formula -> Maybe (HashSet.HashSet AClause)
-- formulaToClauses xs = go xs HashSet.empty
--   where
--     go :: [Id] -> HashSet.HashSet AClause -> Formula -> Maybe (HashSet.HashSet AClause)
--     go xs acc (Atom (App (Sym p) (Sym f)))  
--       | null xs = 
--           pure (HashSet.insert (AClause [] p (Sym f) (Conj [])) acc)
--       | otherwise =
--           empty
--     go xs acc (Atom (App (Sym p) (Var x)))    
--       | x `elem` xs =
--           pure (HashSet.insert (AClause [] p (Var x) (Conj [])) acc)
--       | otherwise =
--           empty
--     go xs acc (Conj fms) =
--       foldM (go xs) acc fms
--     go xs acc (Clause ys (Atom (App (Sym p) tm@(Apps (Sym f) args))) body)
--       | null xs = do
--           ys' <- mapM isMaybeVar args
--           guard (all (`elem` ys) ys')
--           _ <- formulaToClauses ys' body
--           pure (HashSet.insert (AClause ys' p tm body) acc)
--       | otherwise = empty
--     go xs acc (Clause ys (Atom (App (Sym p) tm@(Apps (Var x) args))) body)
--       | x `elem` xs = do
--           ys' <- mapM isMaybeVar args
--           guard (all (`elem` ys) ys')
--           _ <- formulaToClauses ys' body
--           pure (HashSet.insert (AClause ys' p tm body) acc)
--       | otherwise = empty
--     go _ _ _ = empty

-- * Hash Combinators

-- | Hash a value given a map that associates identifiers with their de Buijn index.
type HashFun = HashMap.HashMap Id Int -> Int

-- | Extend a de Buijn environment binding a list of identifiers.
shift :: [Id] -> HashMap.HashMap Id Int -> HashMap.HashMap Id Int
shift xs env =
  foldl'
    (\env' (x, i) -> HashMap.insert x i env')
    (fmap (+ length xs) env)
    (zip xs [0 ..])

hashAtom :: HashFun -> HashFun
hashAtom t env =
  hash ("Atom", t env)

hashTerm :: Term Id -> HashFun
hashTerm (Var x) env =
  case HashMap.lookup x env of
    Nothing -> hash ("Free", x.unique)
    Just i -> hash ("Bound", i)
hashTerm (Sym f) env = hash ("Sym", f)
hashTerm (App fun arg) env =
  hash ("App", hashTerm fun env, hashTerm arg env)

hashConj :: [HashFun] -> HashFun
hashConj fs env =
  hash ("Conj", fmap ($ env) fs)

hashClause :: [Id] -> HashFun -> HashFun -> HashFun
hashClause xs head body env =
  let env' = shift xs env
   in hash ("Clause", head env', body env')

hashExists :: Id -> HashFun -> HashFun
hashExists x body env =
  let env' = shift [x] env
   in hash ("Exists", body env')
