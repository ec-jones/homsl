{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Logical formulas
module HoMSL.Syntax.Formula
  ( Formula,
    pattern Ff,
    pattern Atom,
    pattern Conj,
    pattern Exists,
    pattern Clause,
    pattern AClause,
    groupByHead,
  )
where

import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable
import qualified Data.List as List
import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax.Term

-- * Formulas

-- | General logical formulas.
data Formula = Formula
  { -- | The underlying shape of a formula.
    formulaShape :: FormulaShape,
    -- | The free variables in a formula.
    formulaFreeVars :: IdEnv.Scope,
    -- | Given de Buijn indicies hash the formula.
    formulaHash :: HashFun
  }

-- | The underlying shape of formula.
data FormulaShape
  = Ff_
  | Atom_ Term
  | Conj_ (HashSet.HashSet Formula)
  | Clause_ [Id] Formula Formula
  | Exists_ Id Formula

-- | Equality and hashing check for alpha equivalence.
instance Eq Formula where
  (==) = eqAlpha (IdEnv.empty, IdEnv.empty)
    where
      eqAlpha :: (IdEnv.IdEnv Int, IdEnv.IdEnv Int) -> Formula -> Formula -> Bool
      eqAlpha env Ff Ff = True
      eqAlpha (envl, envr) (Atom t) (Atom s) = eqAlphaTm t s
        where
          eqAlphaTm :: Term -> Term -> Bool
          eqAlphaTm (Var x) (Var y)
            | Just i <- IdEnv.lookup x envl,
              Just j <- IdEnv.lookup y envr =
                i == j
            | Nothing <- IdEnv.lookup x envl,
              Nothing <- IdEnv.lookup y envr =
                x == y
            | otherwise = False
          eqAlphaTm (Sym f) (Sym g) = f == g
          eqAlphaTm (App fun arg) (App fun' arg') =
            eqAlphaTm fun fun' && eqAlphaTm arg arg'
          eqAlphaTm _ _ = False
      eqAlpha env (Conj fs) (Conj gs) =
        all (uncurry (eqAlpha env)) (zip fs gs)
      eqAlpha (envl, envr) (Clause xs body head) (Clause xs' body' head') =
        let envl' = shift xs envl
            envr' = shift xs' envr
         in eqAlpha (envl', envr') body body'
              && eqAlpha (envl', envr') head head'
      eqAlpha (envl, envr) (Exists x body) (Exists x' body') =
        let envl' = shift [x] envl
            envr' = shift [x'] envr
         in eqAlpha (envl', envr') body body'
      eqAlpha _ _ _ = False

-- | Equality and hashing check for alpha equivalence.
instance Hashable Formula where
  hashWithSalt s f =
    hashWithSalt s (formulaHash f IdEnv.empty)

instance Show Formula where
  showsPrec _ Ff = showString "false"
  showsPrec p (Atom t) = showsPrec p t
  showsPrec p (Conj fs) = showParen (p > 3) (showConj fs)
    where
      showConj :: [Formula] -> ShowS
      showConj [] = id
      showConj [f] = showsPrec 3 f
      showConj (f : fs) =
        showsPrec 3 f . showString " /\\ " . showConj fs
  showsPrec p (Clause xs body head) =
    showParen (p > 1) (showForall xs . showBody body . showsPrec 2 head)
    where
      showForall :: [Id] -> ShowS
      showForall [] = id
      showForall xs =
        showString "forall "
          . foldl' (\k x -> k . shows x . showString " ") id xs
          . showString "\b. "

      showBody :: Formula -> ShowS
      showBody (Conj []) = id
      showBody f = showsPrec 2 f . showString " => "
  showsPrec p (Exists x body) =
    showParen (p > 1) (showString "exists " . shows x . showString ". " . showsPrec 2 body)

instance IdEnv.FreeVars Formula where
  freeVars = formulaFreeVars

  subst theta Ff = Ff
  subst theta (Atom t) =
    Atom (IdEnv.subst theta t)
  subst theta (Conj fs) =
    Conj (IdEnv.subst theta <$> fs)
  subst theta f@(Clause xs body head) =
    let (_, xs') = IdEnv.uniqAways (IdEnv.substScope theta <> IdEnv.freeVars f) xs
        theta' = IdEnv.mkRenaming (zip xs xs') <> theta
     in Clause xs' (IdEnv.subst theta' body) (IdEnv.subst theta' head)
  subst theta f@(Exists x body) =
    let (_, x') = IdEnv.uniqAway (IdEnv.substScope theta <> IdEnv.freeVars f) x
        theta' = IdEnv.mkRenaming [(x, x')] <> theta
     in Exists x' (IdEnv.subst theta' body)

-- * Smart constructors

{-# COMPLETE Ff, Atom, Conj, Clause, Exists #-}

{-# COMPLETE AClause, Conj, Exists #-}

-- | False.
pattern Ff :: Formula
pattern Ff <-
  Formula {formulaShape = Ff_}
  where
    Ff =
      Formula
        { formulaShape = Ff_,
          formulaFreeVars = mempty,
          formulaHash = hashFf
        }

-- | An atomic formula.
pattern Atom :: Term -> Formula
pattern Atom t <-
  Formula {formulaShape = Atom_ t}
  where
    Atom t =
      Formula
        { formulaShape = Atom_ t,
          formulaFreeVars = IdEnv.freeVars t,
          formulaHash = hashAtom (hashTerm t)
        }

-- | A conjunction of formulas.
pattern Conj :: [Formula] -> Formula
pattern Conj fs <-
  Formula {formulaShape = Conj_ (HashSet.toList -> fs)}
  where
    Conj = flattenConj mempty

-- | Eliminate nested conjunctions.
flattenConj :: (HashSet.HashSet Formula, IdEnv.Scope) -> [Formula] -> Formula
flattenConj (fs, fvs) []
  | [f] <- HashSet.toList fs = f
  | otherwise =
      Formula
        { formulaShape = Conj_ fs,
          formulaFreeVars = fvs,
          formulaHash = hashConj (formulaHash <$> HashSet.toList fs)
        }
flattenConj fs (Ff : _) = Ff
flattenConj (fs, fvs) (g@(Conj hs) : gs) =
  flattenConj
    ( fs `HashSet.union` HashSet.fromList hs,
      fvs <> IdEnv.freeVars g
    )
    gs
flattenConj (fs, fvs) (g : gs) =
  flattenConj
    ( HashSet.insert g fs,
      fvs <> IdEnv.freeVars g
    )
    gs

-- | A universally quantified clause.
pattern Clause :: [Id] -> Formula -> Formula -> Formula
pattern Clause xs body head <-
  Formula (Clause_ xs body head) _ _
  where
    Clause xs body (Conj heads) =
      -- (ImpAnd)
      Conj [Clause xs body head | head <- heads]
    Clause xs body (Clause ys body' head') =
      -- (ImpImp)
      let (_, ys') = IdEnv.uniqAways (IdEnv.mkScope xs) ys
          rho = IdEnv.mkRenaming (zip ys ys')
       in Clause (xs ++ ys') (Conj [body, IdEnv.subst rho body']) (IdEnv.subst rho head')
    Clause xs body head =
      Formula
        { formulaShape = Clause_ xs body head,
          formulaFreeVars = IdEnv.deleteMany xs (IdEnv.freeVars body <> IdEnv.freeVars head),
          formulaHash = hashClause xs (formulaHash body) (formulaHash head)
        }

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
        (gs, hs) = List.partition (IdEnv.member x . IdEnv.freeVars) fs
    Exists x body
      | x `IdEnv.member` IdEnv.freeVars body =
          Formula
            { formulaShape = Exists_ x body,
              formulaFreeVars = IdEnv.delete x (IdEnv.freeVars body),
              formulaHash = hashExists x (formulaHash body)
            }
      | otherwise = body

-- | An automaton(ish) clause
pattern AClause :: [Id] -> Formula -> Formula -> Formula
pattern AClause xs body head <- (viewAClause -> Just (xs, body, head))

viewAClause :: Formula -> Maybe ([Id], Formula, Formula)
viewAClause Ff = Just ([], Conj [], Ff)
viewAClause (Atom tm) = Just ([], Conj [], Atom tm)
viewAClause (Clause xs body head) = Just (xs, body, head)
viewAClause nonClause = Nothing

-- | Group a list of clauses by head symbol.
groupByHead :: [Formula] -> HashMap.HashMap String (HashSet.HashSet Formula)
groupByHead = foldl' go mempty
  where
    go ::
      HashMap.HashMap String (HashSet.HashSet Formula) ->
      Formula ->
      HashMap.HashMap String (HashSet.HashSet Formula)
    go acc f@(AClause xs body Ff) =
      HashMap.insertWith (<>) "false" (HashSet.singleton f) acc
    go acc f@(AClause xs body (Atom (App (Sym p) _))) =
      HashMap.insertWith (<>) p (HashSet.singleton f) acc
    go acc (AClause _ _ _) = error "Clause is not well-formed!"
    go acc (Conj fs) =
      foldl' go acc fs
    go acc (Exists _ _) = error "Unexpected top-level existential!"

-- * Hash Combinators

-- | Hash a value given a map that associates identifiers with their de Buijn index.
type HashFun = IdEnv.IdEnv Int -> Int

-- | Extend a de Buijn environment binding a list of identifiers.
shift :: [Id] -> IdEnv.IdEnv Int -> IdEnv.IdEnv Int
shift xs env =
  foldl'
    (\env' (x, i) -> IdEnv.insert x i env')
    (fmap (+ length xs) env)
    (zip xs [0 ..])

hashTerm :: Term -> HashFun
hashTerm (Var x) env =
  case IdEnv.lookup x env of
    Nothing -> hash ("Free", idUnique x)
    Just i -> hash ("Bound", i)
hashTerm (Sym f) env = hash ("Sym", f)
hashTerm (App fun arg) env =
  hash ("App", hashTerm fun env, hashTerm arg env)

hashFf :: HashFun
hashFf _ = hash "Ff"

hashAtom :: HashFun -> HashFun
hashAtom t env =
  hash ("Atom", t env)

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
