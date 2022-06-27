{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Memoization of left-recursive non-deterministic functions.
module Control.Monad.Memoization
  ( -- * Memoization Monad
    Memo,
    runMemo,
    memo,

    -- * Reexport
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
#ifdef trace
  (Show a, Show b, Hashable a, Hashable b) =>
#else
  (Hashable a, Hashable b) =>
#endif
  (a -> Memo b s b) ->
  ST s (ST s (HashMap.HashMap a (HashSet.HashSet b)), a -> Memo b s b)
memo f = do
  ref <- newSTRef HashMap.empty
  pure
    ( fmap fst <$> readSTRef ref,
      \x ->
        callCC $ \k -> do
          table <- liftST $ readSTRef ref
          let update e = liftST . writeSTRef ref . HashMap.insert x e
          case HashMap.lookup x table of
            Nothing -> do
              -- Producer Node

#ifdef trace
              traceM ("Producer: " ++ show x)
#endif

              update (HashSet.empty, [k]) table
              y <- f x
              table' <- liftST $ readSTRef ref
              case HashMap.lookup x table' of
                Nothing -> error "Failed to create entry!"
                Just (ys, ks)
                  | y `HashSet.member` ys -> mzero
                  | otherwise -> do
#ifdef trace
                      traceM ("Produce: " ++ show (x, y))
#endif
                      update (HashSet.insert y ys, ks) table'
                      msum [k' y | k' <- ks]
            Just (ys, ks) -> do
              -- Consumer Node

#ifdef trace
              traceM ("Consume: " ++ show x)
#endif

              update (ys, k : ks) table
              msum [k y | y <- HashSet.toList ys]
    )
