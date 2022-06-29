module HoRS.Translation
  ( horsToHoMSL,
  )
where

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import HoMSL.Resolve
import HoMSL.Syntax
import HoRS.Inference
import HoRS.Syntax

-- | Conver a HoRS problem into a clause set.
horsToHoMSL :: [Rule] -> [Transition] -> ClauseSet Formula
horsToHoMSL rules trans =
  let env = inferSorts (rules, trans)
      qs = HashMap.keys $ HashMap.filter isPredicate env
   in mkGoal
        <> foldMap (mkTransitionClause env) trans
        <> foldMap (mkRuleClauses qs env) rules

-- * Constructing HoMSL clauses.

-- | The goal clause.
mkGoal :: ClauseSet Formula
mkGoal =
  ClauseSet $ HashMap.singleton ("false") (HashSet.singleton getFormula)
  where
    getFormula :: Formula
    getFormula = Clause [] Ff (Atom (App (Sym "q0") (Sym "S")))

-- | Make a transition clause.
mkTransitionClause :: HashMap.HashMap String Sort -> Transition -> ClauseSet Formula
mkTransitionClause env (Transition q f rhs) =
  ClauseSet $ HashMap.singleton q (HashSet.singleton getFormula)
  where
    getFormula :: Formula
    getFormula =
      case HashMap.lookup f env of
        Nothing -> error "State not in scope!"
        Just s ->
          let xs = [Id "x" sArg i | (sArg, i) <- zip (sortArgs s) [1 ..]]
              head = Atom (App (Sym q) (Apps (Sym f) (map Var xs)))
              body =
                Conj
                  [ Atom (App (Sym p) (Var (xs !! (i - 1))))
                    | (i, p) <- IntMap.toList rhs
                  ]
           in Clause xs head body

-- | Make clauses for each state and production rule.
mkRuleClauses :: [String] -> HashMap.HashMap String Sort -> Rule -> ClauseSet Formula
mkRuleClauses qs env (Rule f xs rhs) =
  ClauseSet $
    HashMap.fromListWith HashSet.union [(q, HashSet.singleton (getFormula q)) | q <- qs]
  where
    getFormula :: String -> Formula
    getFormula q =
      case HashMap.lookup f env of
        Nothing -> error "State not in scope!"
        Just s ->
          -- xs <-> xs' could probably be made more efficient?
          let xs' = [Id x sArg i | (x, sArg, i) <- zip3 xs (sortArgs s) [1 ..]]
              rho x =
                case List.elemIndex x xs of
                  Nothing -> error "Unbound variable in production rul!"
                  Just i -> xs' !! i
              head = Atom (App (Sym q) (Apps (Sym f) (map Var xs')))
              body = Atom (App (Sym q) (fmap rho rhs))
           in Clause xs' head body
