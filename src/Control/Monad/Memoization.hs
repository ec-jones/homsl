{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Memoization of left-recursive non-deterministic functions.
module Control.Monad.Memoization
  ( -- * Memoization tables
    Table,
    insert,
    lookup,

    -- * Memoization Monad
    Memo,
    runMemo,
    memo,

    -- * Reexports
    Alternative (..),
  )
where

import Control.Applicative
import Control.Monad.Cont
import Control.Monad.Logic
import Control.Monad.ST
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable
import Data.Maybe
import Data.STRef
import Debug.Trace
import Prelude hiding (lookup)

-- * Memoization tables

-- | A table of results.
newtype Table a b
  = Table (HashMap.HashMap a (HashSet.HashSet b))
  deriving stock (Foldable)

instance (Hashable a, Hashable b) => Semigroup (Table a b) where
  Table xs <> Table ys =
    Table (HashMap.unionWith HashSet.union xs ys)

instance (Hashable a, Hashable b) => Monoid (Table a b) where
  mempty = Table HashMap.empty

instance (Show a, Show b) => Show (Table a b) where
  show (Table xs) =
    unlines
      [ show x ++ " -> " ++ show y
        | (x, ys) <- HashMap.toList xs,
          y <- HashSet.toList ys
      ]

-- | Make a table from the internal value.
mkTable :: HashMap.HashMap a (HashSet.HashSet b, c) -> Table a b
mkTable = Table . fmap fst

-- | Insert a value into a table.
insert :: (Hashable a, Hashable b) => a -> b -> Table a b -> Table a b
insert x y (Table xs) =
  Table (HashMap.alter (Just . HashSet.insert y . fromMaybe HashSet.empty) x xs)

-- | Lookup values from the table.
lookup :: Hashable a => a -> Table a b -> [b]
lookup x (Table xs) =
  case HashMap.lookup x xs of
    Nothing -> []
    Just ys -> HashSet.toList ys

-- * Memoization monad.

-- | Memoization monad with ultimate return type @r@ and state thread @s@.
newtype Memo r s a = Memo
  { unMemo :: ContT (Logic r) (ST s) a
  }
  deriving newtype
    ( Functor,
      Applicative,
      Monad,
      MonadCont,
      MonadFail
    )

instance Alternative (Memo r s) where
  empty = Memo $ ContT $ \_ -> pure empty

  Memo m <|> Memo m' = Memo $ ContT $ \k ->
    liftM2 (<|>) (runContT m k) (runContT m' k)

instance MonadPlus (Memo r s) where
  mzero = Memo $ ContT $ \_ -> pure mzero

  Memo m `mplus` Memo m' = Memo $ ContT $ \k ->
    liftM2 mplus (runContT m k) (runContT m' k)

-- | Extract all from the memoization monad.
runMemo :: Memo r s r -> ST s [r]
runMemo k =
  observeAll <$> runContT (unMemo k) (pure . pure)

-- | Lift a stateful computation into the memoization monad.
liftST :: ST s a -> Memo r s a
liftST = Memo . lift

-- | Memoize a non-deterministic function.
memo ::
  (Show a, Show b, Hashable a, Hashable b) =>
  (a -> Memo b s b) ->
  ST s (ST s (Table a b), a -> Memo b s b)
memo f = do
  ref <- newSTRef HashMap.empty
  pure
    ( mkTable <$> readSTRef ref,
      \x ->
        callCC $ \k -> do
          table <- liftST $ readSTRef ref
          let update e = liftST . writeSTRef ref . HashMap.insert x e
          case HashMap.lookup x table of
            Nothing -> do
              -- Producer
              traceM ("Producer: " ++ show x)
              update (HashSet.empty, [k]) table
              y <- f x
              table' <- liftST $ readSTRef ref
              case HashMap.lookup x table' of
                Nothing -> error "Failed to create entry!"
                Just (ys, ks)
                  | y `HashSet.member` ys -> mzero
                  | otherwise -> do
                      traceM ("Produce: " ++ show (x, y))
                      update (HashSet.insert y ys, ks) table'
                      msum [k' y | k' <- ks]
            Just (ys, ks) -> do
              -- Consumer
              traceM ("Consume: " ++ show x)
              update (ys, k : ks) table
              msum [k y | y <- HashSet.toList ys]
    )
