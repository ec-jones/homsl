module HoRS.Translation
  ( horsToHoMSL,
  )
where

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import HoMSL.Syntax
import Data.Char
import HoRS.Inference
import Data.Foldable
import HoRS.Syntax
import Debug.Trace

-- | Conver a HoRS problem into a clause set.
horsToHoMSL :: [Rule] -> [Transition] -> [Formula]
horsToHoMSL rules trans =
  let env = inferSorts (rules, trans)
      -- States
      qs = HashMap.keys $ HashMap.filter isPredicate env
      -- Terminals
      fs = HashMap.keys $ HashMap.filterWithKey (\f s -> 
                                  not (isPredicate s) && isLower (head f)) env
   in foldMap (mkOpTransitionClauses env trans) [ (q, f) | q <- qs, f <- fs ]
        <> foldMap (mkRuleClauses qs env) rules

-- * Constructing HoMSL clauses.

-- | Make a transition clause.
mkOpTransitionClauses :: HashMap.HashMap String Sort -> [Transition] -> (String, String) -> [Formula]
mkOpTransitionClauses env trans (q, f) = 
  let relevantTrans = filter (\(Transition q' f' _) -> q == q' && f == f') trans
   in 
    if null relevantTrans
      then [mkFormula IntMap.empty]
      else [mkFormula rhsOp | rhsOp <- opRHSs (map rhs relevantTrans) ]
  where
    -- Construct the opposite of all right-hand sides.
    opRHSs :: [IntMap.IntMap (HashSet.HashSet String)] -> [IntMap.IntMap (HashSet.HashSet String)]
    opRHSs rhss = do
      -- For each rhs choose an atom that violates the body 
      violators <- mapM (\rhs -> [ IntMap.singleton i (HashSet.singleton p)
                                    | (i, ps) <- IntMap.toList rhs, p <- HashSet.toList ps ]) rhss
      pure (foldr (IntMap.unionWith HashSet.union) IntMap.empty violators)

    -- Make a transition with a given rhs.
    mkFormula :: IntMap.IntMap (HashSet.HashSet String) -> Formula
    mkFormula rhs =
      case HashMap.lookup f env of
        Nothing -> error "State not in scope!"
        Just s ->
          let xs = [Id "x" sArg i | (sArg, i) <- zip (sortArgs s) [1 ..]]
              head = Atom (App (Sym q) (Apps (Sym f) (map Var xs)))
              body =
                Conj
                  [ Atom (App (Sym p) (Var (xs !! (i - 1))))
                    | (i, ps) <- IntMap.toList rhs,
                      p <- HashSet.toList ps
                  ]
           in Clause xs head body

-- | Make clauses for each state and production rule.
mkRuleClauses :: [String] -> HashMap.HashMap String Sort -> Rule -> [Formula]
mkRuleClauses qs env (Rule f xs rhs) = [mkFormula q | q <- qs]
  where
    mkFormula :: String -> Formula
    mkFormula q =
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
