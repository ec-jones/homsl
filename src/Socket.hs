{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Socket
  ( -- * Socket Interface
    Addr,
    SocketM,
    socket,
    connect,
    bind,
    listen,
    accept,
    send,
    receive,
    close,
    fix,

    -- * Analysis
    runAnalysis,

    -- * Testing
    server
  )
where

import qualified Control.Monad.RWS as RWS
import qualified Control.Selective as Selective
import qualified Data.IntMap as IntMap

-- * Socket Interface

-- | Socket addresses
type Addr = Int

-- | Socket DSL
data SocketM soc a
  = Pure a
  | Socket (soc -> SocketM soc a)
  | Connect soc Addr (SocketM soc a)
  | Bind soc Addr (SocketM soc a)
  | Listen soc (SocketM soc a)
  | Accept soc (soc -> Addr -> SocketM soc a)
  | Send soc String (SocketM soc a)
  | Receive soc (String -> SocketM soc a)
  | Close soc (SocketM soc a)
  | -- | Selective interface
    Branch (SocketM soc a) (SocketM soc a)
  | -- | General recursion
    forall b.
    Socket b =>
    Fix
      b
      (b -> (b -> SocketM soc ()) -> SocketM soc ())
      (SocketM soc a)
  | -- | Only used for analysis
    Call Int [SocketId] (SocketM soc a)

deriving stock instance Functor (SocketM soc)

instance Applicative (SocketM soc) where
  pure = Pure

  mf <*> mx = do
    f <- mf
    x <- mx
    pure (f x)

instance Selective.Selective (SocketM soc) where
  select cond m =
    Branch (Pure undefined) (m <*> Pure undefined)

instance Monad (SocketM soc) where
  Pure a >>= k = k a
  Socket k >>= k' =
    Socket (\soc -> k soc >>= k')
  Connect soc addr k >>= k' =
    Connect soc addr (k >>= k')
  Bind soc addr k >>= k' =
    Bind soc addr (k >>= k')
  Listen soc k >>= k' =
    Listen soc (k >>= k')
  Accept soc k >>= k' =
    Accept soc (\x y -> k x y >>= k')
  Send soc msg k >>= k' =
    Send soc msg (k >>= k')
  Receive soc k >>= k' =
    Receive soc (\msg -> k msg >>= k')
  Close soc k >>= k' =
    Close soc (k >>= k')
  Fix x f k >>= k' =
    Fix x f (k >>= k')
  Branch l r >>= k =
    Branch (l >>= k) (r >>= k)
  Call i socs k >>= k' =
    Call i socs (k >>= k')

socket :: SocketM soc soc
socket = Socket Pure

connect :: soc -> Addr -> SocketM soc ()
connect soc addr =
  Connect soc addr (Pure ())

bind :: soc -> Addr -> SocketM soc ()
bind soc addr =
  Bind soc addr (Pure ())

listen :: soc -> SocketM soc ()
listen soc =
  Listen soc (Pure ())

accept :: soc -> SocketM soc (soc, Addr)
accept soc =
  Accept soc (curry Pure)

send :: soc -> String -> SocketM soc ()
send soc msg =
  Send soc msg (Pure ())

receive :: soc -> SocketM soc String
receive soc =
  Receive soc Pure

close :: soc -> SocketM soc ()
close soc =
  Close soc (Pure ())

fix :: Socket b => b -> (b -> (b -> SocketM soc ()) -> SocketM soc ()) -> SocketM soc ()
fix x f =
  Fix x f (Pure ())

-- * Analysis

newtype SocketId
  = SocketId Int
  deriving newtype (Num, Enum, Show)

-- | Analysis monad.
type AnalysisM =
  RWS.RWS
    SocketId -- 0 .. n - 1 socket's in scope
    (IntMap.IntMap (SocketId, String)) -- Top-level definitions
    Int -- Next top-level name.

-- | Fresh top-level name.
fresh :: AnalysisM Int
fresh = do
  fun <- RWS.get
  RWS.put (fun + 1)
  pure fun

-- | Emit a top-level definition.
emitFun :: Int -> String -> AnalysisM ()
emitFun fun defn = do
  nextSoc <- RWS.ask
  RWS.tell (IntMap.singleton fun (nextSoc - 1, defn))

-- | Collect sockets in scope for lambda lifting.
getLiftedArgs :: AnalysisM [SocketId]
getLiftedArgs = do
  nextSoc <- RWS.ask
  pure [0 .. nextSoc - 1]

-- | Mechanism used for extracting socket id's from the arguments to recursive functions.
class Socket a where
  withSocket :: (a -> AnalysisM b) -> AnalysisM b

  getSockets :: a -> [SocketId]

instance Socket SocketId where
  withSocket m = do
    nextSoc <- RWS.ask
    RWS.local (+ 1) (m nextSoc)

  getSockets x = [x]

instance (Socket soc1, Socket soc2) => Socket (soc1, soc2) where
  withSocket m =
    withSocket $ \x ->
      withSocket $ \y ->
        m (x, y)

  getSockets (x, y) =
    getSockets x ++ getSockets y

instance (Socket soc1, Socket soc2, Socket soc3) => Socket (soc1, soc2, soc3) where
  withSocket m =
    withSocket $ \x ->
      withSocket $ \y ->
        withSocket $ \z ->
          m (x, y, z)

  getSockets (x, y, z) =
    getSockets x ++ getSockets y ++ getSockets z

-- | Analyse a socket program.
runAnalysis :: (forall soc. Socket soc => SocketM soc ()) -> (String, IntMap.IntMap (SocketId, String))
runAnalysis m = RWS.evalRWS (go m) 0 0
  where
    go :: SocketM SocketId c -> AnalysisM String
    go (Pure a) = pure "k"
    go (Socket k) = do
      liftedArgs <- getLiftedArgs

      fun <- fresh
      withSocket $ \soc -> do
        defn <- go (k soc)
        emitFun fun defn

      cont <- go (Call fun liftedArgs (Pure ()))
      pure ("socket " ++ cont)
    go (Connect soc _ k) = do
      cont <- go k
      pure ("connect soc_" ++ show soc ++ " (" ++ cont ++ ")")
    go (Bind soc _ k) = do
      cont <- go k
      pure ("bind soc_" ++ show soc ++ " (" ++ cont ++ ")")
    go (Listen soc k) = do
      cont <- go k
      pure ("listen soc_" ++ show soc ++ " (" ++ cont ++ ")")
    go (Accept soc k) = do
      liftedArgs <- getLiftedArgs

      fun <- fresh
      withSocket $ \soc -> do
        defn <- go (k soc dynamic)
        emitFun fun defn

      cont <- go (Call fun liftedArgs (Pure ()))
      pure ("accept soc_" ++ show soc ++ " " ++ cont)
    go (Send soc _ k) = do
      cont <- go k
      pure ("send soc_" ++ show soc ++ " (" ++ cont ++ ")")
    go (Receive soc k) = do
      cont <- go (k dynamic)
      pure ("receive soc_" ++ show soc ++ " (" ++ cont ++ ")")
    go (Close soc k) = do
      cont <- go k
      pure ("close soc_" ++ show soc ++ " (" ++ cont ++ ")")
    go (Branch branch1 branch2) = do
      cont1 <- go branch1
      cont2 <- go branch2
      pure ("branch " ++ " (" ++ cont1 ++ ") (" ++ cont2 ++ ")")
    go (Fix x f k) = do
      liftedArgs <- getLiftedArgs

      fun <- fresh
      withSocket $ \x -> do
        defn <- go (f x (\x -> Call fun (liftedArgs ++ getSockets x) (Pure ())))
        emitFun fun defn

      go (Call fun (liftedArgs ++ getSockets x) k)
    go (Call fun socs k) = do
      cont <- go k
      pure ("func_" ++ show fun ++ " (" ++ cont ++ ")" ++ showArgs socs)

dynamic :: a
dynamic =
  error
    "Static analysis cannot depend on runtime data! \
    \ Try using the selective inferface."

showArgs :: [SocketId] -> String
showArgs xs
  | null xs = ""
  | otherwise = " " ++ unwords (fmap show xs)

-- * Testing

server :: Socket soc => SocketM soc ()
server = do
  soc <- socket
  bind soc 0000
  listen soc
  (x, y) <- accept soc
  fix (x, soc) $ \(x, soc) k -> do
    msg <- receive x
    send soc "pong"
    k (x, soc)

-- socket (func_0 k)
-- func_0: \k soc_0 ->
--  bind soc_0 (listen soc_0 (accept soc_0 (func_1 k soc_0)))
-- func_1: \k soc_0 soc_1 ->
--  func_2 k soc_0 soc_1 soc_1 soc_0
-- func_2: \k soc_0 soc_1 soc_2 soc_3 ->
--  receive soc_2 (send soc_3 (func_2 k soc_0 soc_1 soc_2 soc_3))
