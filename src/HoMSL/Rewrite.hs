{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module HoMSL.Rewrite
  ( ClauseSet,
    tableClauses,
    satisfiable,
  )
where

import Control.Monad.Memoization
import qualified Control.Monad.Memoization as Table
import Control.Monad.ST
import Control.Monad.State
import Data.Foldable
import qualified Data.List as List
import Debug.Trace
import qualified HoMSL.IdEnv as IdEnv
import HoMSL.Syntax

-- TODO: Trace mode.

-- | Clauses grouped by head symbol.
type ClauseSet =
  Table (String, Maybe String) Formula

-- | Create a clause set from a list of formulas.
tableClauses :: [Formula] -> ClauseSet
tableClauses = foldl' go mempty
  where
    go :: ClauseSet -> Formula -> ClauseSet
    go cs (Conj fs) = foldl' go cs fs
    go cs fm@(Clause xs Ff body) =
      Table.insert ("false", Nothing) fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) (Apps (Sym f) _))) body) =
      Table.insert (p, Just f) fm cs
    go cs fm@(Clause xs (Atom (App (Sym p) _)) body) =
      Table.insert (p, Nothing) fm cs
    go cs fm =
      go cs (Clause [] fm (Conj []))

-- | Rewrite the body goal clauses, deriving automaton clauses in the process.
satisfiable :: ClauseSet -> (Bool, ClauseSet)
satisfiable clauses = runST $ mdo
  (getTable, loop) <- memo $ \(p, f) -> do
    -- Select a clause with the given head.
    (xs, head, body) <- msum [pure (viewClause clause) | clause <- Table.lookup (p, f) clauses]
    traceM ("Rewriting: " ++ show (Clause xs head body))

    -- Rewrite the body using the recursively constructed table.
    let scope = IdEnv.fromList [(x, (x, False)) | x <- xs]
    (body', (_, subst)) <- runStateT (rewrite False loop body) (scope, mempty)

    -- There should be no existentials in the top-level.
    unless (IdEnv.null (substMap subst)) $
      error "Uncaught existential variable!"

    pure (Clause xs head body')

  -- Attempt to rewrite any goal clauses.
  res <- runMemo (loop ("false", Nothing))

  -- Gather all clauses produced in rewriting goals.
  table <- getTable
  pure (null res, table)

-- | Non-determinstically rewrite a goal formula into automaton form using the table.
-- The first parameter indicates if the formula is to appear as the head of a nested clause.
rewrite ::
  Bool ->
  ((String, Maybe String) -> Memo Formula s Formula) ->
  Formula ->
  StateT (IdEnv.IdEnv (Id, Bool), Subst) (Memo Formula s) Formula
rewrite nested table Ff = pure Ff
rewrite nested table (Atom tm@(App (Sym p) arg)) = do
  (vars, theta) <- get
  case subst theta arg of
    Apps (Var y) ss
      | any (deepOrExistential vars) ss,
        not (existential vars y) -> do
          -- (Assm)
          selected@(viewClause -> (ys, head, body)) <-
            lift $ table (p, funSymbol arg)
          let (ys', xs) = List.splitAt (length ys - length ss) ys
          guard
            ( length ys >= length ss
                && sortArgs (idSort y) == fmap idSort xs
            )

          let (_, xs') = uniqAways (fmap fst vars) xs
              rho = mkRenaming (zip xs xs')
              inst = mkSubst (zip xs' ss)
              body' = restrictBody xs' (subst rho body)
              head' = App (Sym p) (Apps (Var y) (map Var xs'))

          rewrite nested table $
            Conj
              [ subst inst body',
                Clause xs' (Atom head') body'
              ]
      | nested,
        not (null ss),
        not (existential vars y) ->
          pure (Atom (App (Sym p) arg))
    nonHo
      | nested || deepOrExistential vars arg -> do
          -- (ExInst) and (Step/Refl)
          clause@(viewClause -> (xs, Atom head, body)) <-
            lift $ table (p, funSymbol arg)
          inst <- match xs head tm
          rewrite nested table (subst inst body)
      | otherwise -> pure (Atom (App (Sym p) nonHo))
rewrite nested table (Atom _) = error "Term is not a valid atom!"
rewrite nested table (Conj fs) =
  Conj <$> mapM (rewrite nested table) fs
rewrite nested table (Exists x body) = do
  (vars, theta) <- get
  put (IdEnv.insert x (x, True) vars, theta)
  body' <- rewrite nested table body
  (vars', theta') <- get
  put (IdEnv.delete x vars', deleteSubst [x] theta')
  pure body'
rewrite nested table (Clause xs head body)
  | all (`notElem` xs) (freeVars head) =
      -- (Scope1)
      pure head
  | otherwise = do
      -- Locally extend table with clauses in the body.
      let table' (p, f) =
            table (p, f)
              <|> msum
                [ pure clause
                  | clause <- Table.lookup (p, f) (tableClauses [body])
                ]
      (vars, theta) <- get
      put
        ( IdEnv.fromList [(x, (x, False)) | x <- xs] <> vars,
          deleteSubst xs theta
        )
      head' <- rewrite True table' head
      (vars', theta') <- get
      put (IdEnv.deleteMany xs vars', theta')
      if head == head'
        then pure (Clause xs head' body)
        else rewrite nested table (Clause xs head' body)

-- | @matchHead xs head tm@ finds instance of head that instantitates xs.
-- It may also instantiate existential variables from tm.
-- The head is assumed to be shallow and linear.
match :: [Id] -> Term Id -> Term Id -> StateT (IdEnv.IdEnv (Id, Bool), Subst) (Memo Formula s) Subst
match xs (Var x) t
  | x `elem` xs = pure (mkSubst [(x, t)])
  | t == Var x = pure mempty
  | otherwise = empty
match xs (Sym f) (Sym g)
  | f == g = pure mempty
  | otherwise = empty
match xs (App fun arg) (App fun' arg') = do
  -- Decomposition
  theta <- match xs fun fun'
  theta' <- match xs arg arg'
  -- Linearity ensure the substitutions are consistent.
  pure (theta <> theta')
match xs t@(Apps (Sym fun) args) (Var x) = do
  (vars, theta) <- get
  case lookupSubst x theta of
    Nothing
      | existential vars x -> do
          -- Expand x with fresh arguments.
          let scope = fmap fst vars
              (_, xs) = uniqAways scope [Id "" (idSort arg) i | (Var arg, i) <- zip args [0 ..]]
              vars' = [(x, (x, True)) | x <- xs]
              t' = Apps (Sym fun) (fmap Var xs)
          put (IdEnv.fromList vars' <> vars, mkSubst [(x, t)] <> theta)
          match xs t t' -- Match arguments
      | otherwise -> empty
    Just t' ->
      match xs t t'
match _ _ _ = empty

-- | Check if a term is an existential variable or an application.
deepOrExistential :: IdEnv.IdEnv (Id, Bool) -> Term Id -> Bool
deepOrExistential vars (Var x) = existential vars x
deepOrExistential vars noNVar = True

-- | Check if an identifier is existential or not.
existential :: IdEnv.IdEnv (Id, Bool) -> Id -> Bool
existential vars x =
  case IdEnv.lookup x vars of
    Nothing -> error ("Variable not in scope: " ++ show x)
    Just (_, p) -> p

-- | Remove irrelevant atoms from the body of automaton clause.
restrictBody :: [Id] -> Formula -> Formula
restrictBody xs = Conj . go []
  where
    go :: [Formula] -> Formula -> [Formula]
    go acc f@(Atom tm)
      | all (`elem` xs) (freeVars tm) = f : acc
      | otherwise = acc
    go acc (Conj fs) =
      foldl' go acc fs
    go acc f@(Clause ys head body)
      -- We assume the body only concerns ys.
      | all (`elem` (xs ++ ys)) (freeVars head) = f : acc
      | otherwise = acc
    go acc _ =
      error "Non-automaton clause!"
