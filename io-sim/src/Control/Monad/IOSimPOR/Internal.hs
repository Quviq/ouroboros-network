{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTSyntax                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}

{-# OPTIONS_GHC -Wno-orphans            #-}
-- incomplete uni patterns in 'schedule' (when interpreting 'StmTxCommitted')
-- and 'reschedule'.
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Control.Monad.IOSimPOR.Internal (
  IOSim (..),
  SimM,
  runIOSim,
  runSimTraceST,
  traceM,
  traceSTM,
  STM,
  STMSim,
  SimSTM,
  setCurrentTime,
  unshareClock,
  TimeoutException (..),
  EventlogEvent (..),
  EventlogMarker (..),
  ThreadId,
  ThreadLabel,
  Labelled (..),
  Trace (..),
  TraceEvent (..),
  liftST,
  execReadTVar,
  controlSimTraceST,
  ScheduleControl(..),
  ScheduleMod(..)
  ) where

import           Prelude hiding (read)

import           Data.Ord
import           Data.Dynamic (Dynamic, toDyn)
import           Data.Function(on)
import           Data.Foldable (traverse_)
import qualified Data.List as List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.OrdPSQ (OrdPSQ)
import qualified Data.OrdPSQ as PSQ
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Time (UTCTime (..), fromGregorian)
import           Data.Typeable (Typeable)
import           Quiet (Quiet (..))
import           GHC.Generics (Generic)
import           GHC.Show

import           Control.Applicative (Alternative (..), liftA2)
import           Control.Exception (ErrorCall (..), assert,
                     asyncExceptionFromException, asyncExceptionToException)
import           Control.Monad (MonadPlus, join)
import qualified System.IO.Error as IO.Error (userError)

import           Control.Monad (when)
import           Control.Monad.ST.Lazy
import           Control.Monad.ST.Lazy.Unsafe (unsafeIOToST)
import qualified Control.Monad.ST.Strict as StrictST
import           Data.STRef.Lazy

import qualified Control.Monad.Catch as Exceptions
import qualified Control.Monad.Fail as Fail

import           Control.Monad.Class.MonadAsync hiding (Async)
import qualified Control.Monad.Class.MonadAsync as MonadAsync
import           Control.Monad.Class.MonadEventlog
import           Control.Monad.Class.MonadFork hiding (ThreadId)
import qualified Control.Monad.Class.MonadFork as MonadFork
import           Control.Monad.Class.MonadSay
import           Control.Monad.Class.MonadST
import           Control.Monad.Class.MonadSTM hiding (STM, TVar)
import qualified Control.Monad.Class.MonadSTM as MonadSTM
import           Control.Monad.Class.MonadThrow as MonadThrow
import           Control.Monad.Class.MonadTime
import           Control.Monad.Class.MonadTimer
import           Control.Monad.Class.MonadTest

import qualified Debug.Trace as Debug

{-# ANN module "HLint: ignore Use readTVarIO" #-}
newtype IOSim s a = IOSim { unIOSim :: forall r. (a -> SimA s r) -> SimA s r }

type SimM s = IOSim s
{-# DEPRECATED SimM "Use IOSim" #-}

runIOSim :: IOSim s a -> SimA s a
runIOSim (IOSim k) = k Return

traceM :: Typeable a => a -> IOSim s ()
traceM x = IOSim $ \k -> Output (toDyn x) (k ())

traceSTM :: Typeable a => a -> STMSim s ()
traceSTM x = STM $ \k -> OutputStm (toDyn x) (k ())

data SimA s a where
  Return       :: a -> SimA s a

  Say          :: String -> SimA s b -> SimA s b
  Output       :: Dynamic -> SimA s b -> SimA s b

  LiftST       :: StrictST.ST s a -> (a -> SimA s b) -> SimA s b

  GetMonoTime  :: (Time    -> SimA s b) -> SimA s b
  GetWallTime  :: (UTCTime -> SimA s b) -> SimA s b
  SetWallTime  ::  UTCTime -> SimA s b  -> SimA s b
  UnshareClock :: SimA s b -> SimA s b

  NewTimeout   :: DiffTime -> (Timeout (IOSim s) -> SimA s b) -> SimA s b
  UpdateTimeout:: Timeout (IOSim s) -> DiffTime -> SimA s b -> SimA s b
  CancelTimeout:: Timeout (IOSim s) -> SimA s b -> SimA s b

  Throw        :: SomeException -> SimA s a
  Catch        :: Exception e =>
                  SimA s a -> (e -> SimA s a) -> (a -> SimA s b) -> SimA s b
  Evaluate     :: a -> (a -> SimA s b) -> SimA s b

  Fork         :: IOSim s () -> (ThreadId -> SimA s b) -> SimA s b
  GetThreadId  :: (ThreadId -> SimA s b) -> SimA s b
  LabelThread  :: ThreadId -> String -> SimA s b -> SimA s b

  Atomically   :: STM  s a -> (a -> SimA s b) -> SimA s b

  ThrowTo      :: SomeException -> ThreadId -> SimA s a -> SimA s a
  SetMaskState :: MaskingState  -> IOSim s a -> (a -> SimA s b) -> SimA s b
  GetMaskState :: (MaskingState -> SimA s b) -> SimA s b

  ExploreRaces :: SimA s b -> SimA s b


newtype STM s a = STM { unSTM :: forall r. (a -> StmA s r) -> StmA s r }

runSTM :: STM s a -> StmA s a
runSTM (STM k) = k ReturnStm

data StmA s a where
  ReturnStm    :: a -> StmA s a
  ThrowStm     :: SomeException -> StmA s a

  NewTVar      :: Maybe String -> x -> (TVar s x -> StmA s b) -> StmA s b
  LabelTVar    :: String -> TVar s a -> StmA s b -> StmA s b
  ReadTVar     :: TVar s a -> (a -> StmA s b) -> StmA s b
  WriteTVar    :: TVar s a ->  a -> StmA s b  -> StmA s b
  Retry        :: StmA s b
  OrElse       :: StmA s a -> StmA s a -> (a -> StmA s b) -> StmA s b

  SayStm       :: String -> StmA s b -> StmA s b
  OutputStm    :: Dynamic -> StmA s b -> StmA s b

-- Exported type
type STMSim = STM

type SimSTM = STM
{-# DEPRECATED SimSTM "Use STMSim" #-}

data MaskingState = Unmasked | MaskedInterruptible | MaskedUninterruptible
  deriving (Eq, Ord, Show)

--
-- Monad class instances
--

instance Functor (IOSim s) where
    {-# INLINE fmap #-}
    fmap f = \d -> IOSim $ \k -> unIOSim d (k . f)

instance Applicative (IOSim s) where
    {-# INLINE pure #-}
    pure = \x -> IOSim $ \k -> k x

    {-# INLINE (<*>) #-}
    (<*>) = \df dx -> IOSim $ \k ->
                        unIOSim df (\f -> unIOSim dx (\x -> k (f x)))

    {-# INLINE (*>) #-}
    (*>) = \dm dn -> IOSim $ \k -> unIOSim dm (\_ -> unIOSim dn k)

instance Monad (IOSim s) where
    return = pure

    {-# INLINE (>>=) #-}
    (>>=) = \dm f -> IOSim $ \k -> unIOSim dm (\m -> unIOSim (f m) k)

    {-# INLINE (>>) #-}
    (>>) = (*>)

#if !(MIN_VERSION_base(4,13,0))
    fail = Fail.fail
#endif

instance Semigroup a => Semigroup (IOSim s a) where
    (<>) = liftA2 (<>)

instance Monoid a => Monoid (IOSim s a) where
    mempty = pure mempty

#if !(MIN_VERSION_base(4,11,0))
    mappend = liftA2 mappend
#endif

instance Fail.MonadFail (IOSim s) where
  fail msg = IOSim $ \_ -> Throw (toException (IO.Error.userError msg))


instance Functor (STM s) where
    {-# INLINE fmap #-}
    fmap f = \d -> STM $ \k -> unSTM d (k . f)

instance Applicative (STM s) where
    {-# INLINE pure #-}
    pure = \x -> STM $ \k -> k x

    {-# INLINE (<*>) #-}
    (<*>) = \df dx -> STM $ \k ->
                        unSTM df (\f -> unSTM dx (\x -> k (f x)))

    {-# INLINE (*>) #-}
    (*>) = \dm dn -> STM $ \k -> unSTM dm (\_ -> unSTM dn k)

instance Monad (STM s) where
    return = pure

    {-# INLINE (>>=) #-}
    (>>=) = \dm f -> STM $ \k -> unSTM dm (\m -> unSTM (f m) k)

    {-# INLINE (>>) #-}
    (>>) = (*>)

#if !(MIN_VERSION_base(4,13,0))
    fail = Fail.fail
#endif

instance Fail.MonadFail (STM s) where
  fail msg = STM $ \_ -> ThrowStm (toException (ErrorCall msg))

instance Alternative (STM s) where
    empty = retry
    (<|>) = orElse

instance MonadPlus (STM s) where

instance MonadSay (IOSim s) where
  say msg = IOSim $ \k -> Say msg (k ())

instance MonadThrow (IOSim s) where
  throwIO e = IOSim $ \_ -> Throw (toException e)

instance MonadEvaluate (IOSim s) where
  evaluate a = IOSim $ \k -> Evaluate a k

instance Exceptions.MonadThrow (IOSim s) where
  throwM = MonadThrow.throwIO

instance MonadThrow (STM s) where
  throwIO e = STM $ \_ -> ThrowStm (toException e)

  -- Since these involve re-throwing the exception and we don't provide
  -- CatchSTM at all, then we can get away with trivial versions:
  bracket before after thing = do
    a <- before
    r <- thing a
    _ <- after a
    return r

  finally thing after = do
    r <- thing
    _ <- after
    return r

instance Exceptions.MonadThrow (STM s) where
  throwM = MonadThrow.throwIO

instance MonadCatch (IOSim s) where
  catch action handler =
    IOSim $ \k -> Catch (runIOSim action) (runIOSim . handler) k

instance Exceptions.MonadCatch (IOSim s) where
  catch = MonadThrow.catch

instance MonadMask (IOSim s) where
  mask action = do
      b <- getMaskingState
      case b of
        Unmasked              -> block $ action unblock
        MaskedInterruptible   -> action block
        MaskedUninterruptible -> action blockUninterruptible

  uninterruptibleMask action = do
      b <- getMaskingState
      case b of
        Unmasked              -> blockUninterruptible $ action unblock
        MaskedInterruptible   -> blockUninterruptible $ action block
        MaskedUninterruptible -> action blockUninterruptible

instance Exceptions.MonadMask (IOSim s) where
  mask                = MonadThrow.mask
  uninterruptibleMask = MonadThrow.uninterruptibleMask

  generalBracket acquire release use =
    mask $ \unmasked -> do
      resource <- acquire
      b <- unmasked (use resource) `catch` \e -> do
        _ <- release resource (Exceptions.ExitCaseException e)
        throwIO e
      c <- release resource (Exceptions.ExitCaseSuccess b)
      return (b, c)


getMaskingState :: IOSim s MaskingState
unblock, block, blockUninterruptible :: IOSim s a -> IOSim s a

getMaskingState        = IOSim  GetMaskState
unblock              a = IOSim (SetMaskState Unmasked a)
block                a = IOSim (SetMaskState MaskedInterruptible a)
blockUninterruptible a = IOSim (SetMaskState MaskedUninterruptible a)

instance MonadThread (IOSim s) where
  type ThreadId (IOSim s) = ThreadId
  myThreadId       = IOSim $ \k -> GetThreadId k
  labelThread t l  = IOSim $ \k -> LabelThread t l (k ())

instance MonadFork (IOSim s) where
  forkIO task        = IOSim $ \k -> Fork task k
  forkIOWithUnmask f = forkIO (f unblock)
  throwTo tid e      = IOSim $ \k -> ThrowTo (toException e) tid (k ())

instance MonadTest (IOSim s) where
  exploreRaces       = IOSim $ \k -> ExploreRaces (k ())

instance MonadSay (STMSim s) where
  say msg = STM $ \k -> SayStm msg (k ())

instance MonadSTMTx (STM s)
                    (TVar s)
                    (TMVarDefault   (IOSim s))
                    (TQueueDefault  (IOSim s))
                    (TBQueueDefault (IOSim s)) where
  newTVar         x = STM $ \k -> NewTVar Nothing x k
  readTVar   tvar   = STM $ \k -> ReadTVar tvar k
  writeTVar  tvar x = STM $ \k -> WriteTVar tvar x (k ())
  retry             = STM $ \_ -> Retry
  orElse        a b = STM $ \k -> OrElse (runSTM a) (runSTM b) k

  newTMVar          = newTMVarDefault
  newEmptyTMVar     = newEmptyTMVarDefault
  takeTMVar         = takeTMVarDefault
  tryTakeTMVar      = tryTakeTMVarDefault
  putTMVar          = putTMVarDefault
  tryPutTMVar       = tryPutTMVarDefault
  readTMVar         = readTMVarDefault
  tryReadTMVar      = tryReadTMVarDefault
  swapTMVar         = swapTMVarDefault
  isEmptyTMVar      = isEmptyTMVarDefault

  newTQueue         = newTQueueDefault
  readTQueue        = readTQueueDefault
  tryReadTQueue     = tryReadTQueueDefault
  writeTQueue       = writeTQueueDefault
  isEmptyTQueue     = isEmptyTQueueDefault

  newTBQueue        = newTBQueueDefault
  readTBQueue       = readTBQueueDefault
  tryReadTBQueue    = tryReadTBQueueDefault
  flushTBQueue      = flushTBQueueDefault
  writeTBQueue      = writeTBQueueDefault
  lengthTBQueue     = lengthTBQueueDefault
  isEmptyTBQueue    = isEmptyTBQueueDefault
  isFullTBQueue     = isFullTBQueueDefault

instance MonadLabelledSTMTx (STM s)
                            (TVar s)
                            (TMVarDefault   (IOSim s))
                            (TQueueDefault  (IOSim s))
                            (TBQueueDefault (IOSim s)) where
  labelTVar tvar label = STM $ \k -> LabelTVar label tvar (k ())
  labelTMVar   = labelTMVarDefault
  labelTQueue  = labelTQueueDefault
  labelTBQueue = labelTBQueueDefault

instance MonadLabelledSTM (IOSim s) where

instance MonadSTM (IOSim s) where
  type STM     (IOSim s) = STM s
  type TVar    (IOSim s) = TVar s
  type TMVar   (IOSim s) = TMVarDefault (IOSim s)
  type TQueue  (IOSim s) = TQueueDefault (IOSim s)
  type TBQueue (IOSim s) = TBQueueDefault (IOSim s)

  atomically action = IOSim $ \k -> Atomically action k

  newTMVarIO        = newTMVarIODefault
  newEmptyTMVarIO   = newEmptyTMVarIODefault

data Async s a = Async !ThreadId (STM s (Either SomeException a))

instance Eq (Async s a) where
    Async tid _ == Async tid' _ = tid == tid'

instance Ord (Async s a) where
    compare (Async tid _) (Async tid' _) = compare tid tid'

instance Functor (Async s) where
  fmap f (Async tid a) = Async tid (fmap f <$> a)

instance MonadAsyncSTM (Async s)
                       (STM s)
                       (TVar s)
                       (TMVarDefault   (IOSim s))
                       (TQueueDefault  (IOSim s))
                       (TBQueueDefault (IOSim s)) where
  waitCatchSTM (Async _ w) = w
  pollSTM      (Async _ w) = (Just <$> w) `orElse` return Nothing

instance MonadAsync (IOSim s) where
  type Async (IOSim s) = Async s

  async action = do
    var <- newEmptyTMVarIO
    tid <- mask $ \restore ->
             forkIO $ try (restore action) >>= atomically . putTMVar var
    return (Async tid (readTMVar var))

  asyncThreadId _proxy (Async tid _) = tid

  cancel a@(Async tid _) = throwTo tid AsyncCancelled <* waitCatch a
  cancelWith a@(Async tid _) e = throwTo tid e <* waitCatch a

  asyncWithUnmask k = async (k unblock)

instance MonadST (IOSim s) where
  withLiftST f = f liftST

liftST :: StrictST.ST s a -> IOSim s a
liftST action = IOSim $ \k -> LiftST action k

instance MonadMonotonicTime (IOSim s) where
  getMonotonicTime = IOSim $ \k -> GetMonoTime k

instance MonadTime (IOSim s) where
  getCurrentTime   = IOSim $ \k -> GetWallTime k

-- | Set the current wall clock time for the thread's clock domain.
--
setCurrentTime :: UTCTime -> IOSim s ()
setCurrentTime t = IOSim $ \k -> SetWallTime t (k ())

-- | Put the thread into a new wall clock domain, not shared with the parent
-- thread. Changing the wall clock time in the new clock domain will not affect
-- the other clock of other threads. All threads forked by this thread from
-- this point onwards will share the new clock domain.
--
unshareClock :: IOSim s ()
unshareClock = IOSim $ \k -> UnshareClock (k ())

instance MonadDelay (IOSim s) where
  -- Use default in terms of MonadTimer

instance MonadTimer (IOSim s) where
  data Timeout (IOSim s) = Timeout !(TVar s TimeoutState) !(TVar s Bool) !TimeoutId
                         -- ^ a timeout; we keep both 'TVar's to support
                         -- `newTimer` and 'registerTimeout'.
                         | NegativeTimeout !TimeoutId
                         -- ^ a negative timeout

  readTimeout (Timeout var _bvar _key) = readTVar var
  readTimeout (NegativeTimeout _key)   = pure TimeoutCancelled

  newTimeout      d = IOSim $ \k -> NewTimeout      d k
  updateTimeout t d = IOSim $ \k -> UpdateTimeout t d (k ())
  cancelTimeout t   = IOSim $ \k -> CancelTimeout t   (k ())

  timeout d action
    | d <  0    = Just <$> action
    | d == 0    = return Nothing
    | otherwise = do
        pid <- myThreadId
        t@(Timeout _ _ tid) <- newTimeout d
        handleJust
          (\(TimeoutException tid') -> if tid' == tid
                                         then Just ()
                                         else Nothing)
          (\_ -> return Nothing) $
          bracket
            (forkIO $ do
                fired <- atomically $ awaitTimeout t
                when fired $ throwTo pid (TimeoutException tid))
            (\pid' -> do
                  cancelTimeout t
                  throwTo pid' AsyncCancelled)
            (\_ -> Just <$> action)

  registerDelay d = IOSim $ \k -> NewTimeout d (\(Timeout _var bvar _) -> k bvar)

newtype TimeoutException = TimeoutException TimeoutId deriving Eq

instance Show TimeoutException where
    show _ = "<<timeout>>"

instance Exception TimeoutException where
  toException   = asyncExceptionToException
  fromException = asyncExceptionFromException

-- | Wrapper for Eventlog events so they can be retrieved from the trace with
-- 'selectTraceEventsDynamic'.
newtype EventlogEvent = EventlogEvent String

-- | Wrapper for Eventlog markers so they can be retrieved from the trace with
-- 'selectTraceEventsDynamic'.
newtype EventlogMarker = EventlogMarker String

instance MonadEventlog (IOSim s) where
  traceEventIO = traceM . EventlogEvent
  traceMarkerIO = traceM . EventlogMarker

--
-- Simulation interpreter
--

data Thread s a = Thread {
    threadId      :: !ThreadId,
    threadControl :: !(ThreadControl s a),
    threadBlocked :: !Bool,
    threadDone    :: !Bool,
    threadMasking :: !MaskingState,
    -- other threads blocked in a ThrowTo to us because we are or were masked
    threadThrowTo :: ![(SomeException, Labelled ThreadId, VectorClock)],
    threadClockId :: !ClockId,
    threadLabel   :: Maybe ThreadLabel,
    threadNextTId :: !Int,
    threadStep    :: !Int,
    threadVClock  :: VectorClock,
    threadEffect  :: Effect,  -- in the current step
    threadRacy    :: !Bool
  }
  deriving Show

-- We hide the type @b@ here, so it's useful to bundle these two parts
-- together, rather than having Thread have an extential type, which
-- makes record updates awkward.
data ThreadControl s a where
  ThreadControl :: SimA s b
                -> ControlStack s b a
                -> ThreadControl s a

instance Show (ThreadControl s a) where
  show _ = "..."

data ControlStack s b a where
  MainFrame  :: ControlStack s a  a
  ForkFrame  :: ControlStack s () a
  MaskFrame  :: (b -> SimA s c)         -- subsequent continuation
             -> MaskingState            -- thread local state to restore
             -> ControlStack s c a
             -> ControlStack s b a
  CatchFrame :: Exception e
             => (e -> SimA s b)         -- exception continuation
             -> (b -> SimA s c)         -- subsequent continuation
             -> ControlStack s c a
             -> ControlStack s b a

instance Show (ControlStack s b a) where
  show = show . dash
    where dash :: ControlStack s' b' a' -> ControlStackDash
          dash MainFrame = MainFrame'
          dash ForkFrame = ForkFrame'
          dash (MaskFrame _ m s) = MaskFrame' m (dash s)
          dash (CatchFrame _ _ s) = CatchFrame' (dash s)

data ControlStackDash =
    MainFrame'
  | ForkFrame'
  | MaskFrame' MaskingState ControlStackDash
  | CatchFrame' ControlStackDash
  deriving Show

data    ThreadId    = ThreadId  [Int]
                    | TestThreadId [Int]    -- test threads have higher priority
  deriving (Eq, Ord, Show)
  
newtype TVarId      = TVarId    Int   deriving (Eq, Ord, Enum, Show)
newtype TimeoutId   = TimeoutId Int   deriving (Eq, Ord, Enum, Show)
newtype ClockId     = ClockId   [Int] deriving (Eq, Ord, Show)
newtype VectorClock = VectorClock (Map ThreadId Int) deriving Show

isTestThreadId (TestThreadId _) = True
isTestThreadId _                = False

unTimeoutId :: TimeoutId -> Int
unTimeoutId (TimeoutId a) = a

bottomVClock :: VectorClock
bottomVClock = VectorClock Map.empty

insertVClock :: ThreadId -> Int -> VectorClock -> VectorClock
insertVClock tid !step (VectorClock m) = VectorClock (Map.insert tid step m)

lubVClock :: VectorClock -> VectorClock -> VectorClock
lubVClock (VectorClock m) (VectorClock m') = VectorClock (Map.unionWith max m m')

hbfVClock :: VectorClock -> VectorClock -> Bool
hbfVClock (VectorClock m) (VectorClock m') = Map.isSubmapOfBy (<=) m m'

hbfStep :: ThreadId -> Int -> VectorClock -> Bool
hbfStep tid tstep (VectorClock m) = Just tstep <= Map.lookup tid m

type ThreadLabel = String
type TVarLabel   = String

data Labelled a = Labelled {
    l_labelled :: !a,
    l_label    :: !(Maybe String)
  }
  deriving (Eq, Ord, Generic)
  deriving Show via Quiet (Labelled a)

labelledTVarId :: TVar s a -> ST s (Labelled TVarId)
labelledTVarId TVar { tvarId, tvarLabel } = (Labelled tvarId) <$> readSTRef tvarLabel

labelledThreads :: Map ThreadId (Thread s a) -> [Labelled ThreadId]
labelledThreads threadMap =
    -- @Map.foldr'@ (and alikes) are not strict enough, to not retain the
    -- original thread map we need to evaluate the spine of the list.
    -- TODO: https://github.com/haskell/containers/issues/749
    Map.foldr'
      (\Thread { threadId, threadLabel } !acc -> Labelled threadId threadLabel : acc)
      [] threadMap


-- | 'Trace' is a recursive data type, it is the trace of a 'IOSim' computation.
-- The trace will contain information about thread sheduling, blocking on
-- 'TVar's, and other internal state changes of 'IOSim'.  More importantly it
-- also supports traces generated by the computation with 'say' (which
-- corresponds to using 'putStrLn' in 'IO'), 'traceEventM', or dynamically typed
-- traces with 'traceM' (which generalise the @base@ library
-- 'Debug.Trace.traceM')
--
-- It also contains information on races discovered.
--
-- See also: 'traceEvents', 'traceResult', 'selectTraceEvents',
-- 'selectTraceEventsDynamic' and 'printTraceEventsSay'.
--
data Trace a = Trace !Time !ThreadId !(Maybe ThreadLabel) !TraceEvent (Trace a)
             | TraceRacesFound    [ScheduleControl]                   (Trace a)
             | TraceMainReturn    !Time a             ![Labelled ThreadId]
             | TraceMainException !Time SomeException ![Labelled ThreadId]
             | TraceDeadlock      !Time               ![Labelled ThreadId]
             | TraceLoop
  deriving Show

data TraceEvent
  = EventSay  String
  | EventLog  Dynamic

  | EventThrow          SomeException
  | EventThrowTo        SomeException ThreadId -- This thread used ThrowTo
  | EventThrowToBlocked                        -- The ThrowTo blocked
  | EventThrowToWakeup                         -- The ThrowTo resumed
  | EventThrowToUnmasked (Labelled ThreadId)   -- A pending ThrowTo was activated

  | EventThreadForked    ThreadId
  | EventThreadFinished                  -- terminated normally
  | EventThreadUnhandled SomeException   -- terminated due to unhandled exception

  | EventTxCommitted   [Labelled TVarId] -- tx wrote to these
                       [TVarId]          -- and created these
  | EventTxAborted
  | EventTxBlocked     [Labelled TVarId] -- tx blocked reading these
  | EventTxWakeup      [Labelled TVarId] -- changed vars causing retry

  | EventTimerCreated   TimeoutId TVarId Time
  | EventTimerUpdated   TimeoutId        Time
  | EventTimerCancelled TimeoutId
  | EventTimerExpired   TimeoutId
  deriving Show


-- | Timers mutable variables.  First one supports 'newTimeout' api, the second
-- one 'registerDelay'.
--
data TimerVars s = TimerVars !(TVar s TimeoutState) !(TVar s Bool)


-- | Internal state.
--
data SimState s a = SimState {
       runqueue :: ![ThreadId],
       -- | All threads other than the currently running thread: both running
       -- and blocked threads.
       threads  :: !(Map ThreadId (Thread s a)),
       -- | current time
       curTime  :: !Time,
       -- | ordered list of timers
       timers   :: !(OrdPSQ TimeoutId Time (TimerVars s)),
       -- | list of clocks
       clocks   :: !(Map ClockId UTCTime),
       nextVid  :: !TVarId,     -- ^ next unused 'TVarId'
       nextTmid :: !TimeoutId,  -- ^ next unused 'TimeoutId'
       -- | previous steps (which we may race with).
       -- Note this is *lazy*, so that we don't compute races we will not reverse.
       races    :: Races,
       -- | control the schedule followed, and initial value
       control  :: !ScheduleControl,
       control0 :: !ScheduleControl

     }

initialState :: SimState s a
initialState =
    SimState {
      runqueue = [],
      threads  = Map.empty,
      curTime  = Time 0,
      timers   = PSQ.empty,
      clocks   = Map.singleton (ClockId []) epoch1970,
      nextVid  = TVarId 0,
      nextTmid = TimeoutId 0,
      races    = noRaces,
      control  = ControlDefault,
      control0 = ControlDefault
    }
  where
    epoch1970 = UTCTime (fromGregorian 1970 1 1) 0

invariant :: Maybe (Thread s a) -> SimState s a -> Bool

invariant (Just running) simstate@SimState{runqueue,threads,clocks} =
    not (threadBlocked running)
 && threadId running `Map.notMember` threads
 && threadId running `List.notElem` runqueue
 && threadClockId running `Map.member` clocks
 && invariant Nothing simstate

invariant Nothing SimState{runqueue,threads,clocks} =
    all (`Map.member` threads) runqueue
 && and [ (threadBlocked t || threadDone t) == (threadId t `notElem` runqueue)
        | t <- Map.elems threads ]
 && and (zipWith (>) runqueue (drop 1 runqueue))
 && and [ threadClockId t `Map.member` clocks
        | t <- Map.elems threads ]

-- | Interpret the simulation monotonic time as a 'NominalDiffTime' since
-- the start.
timeSiceEpoch :: Time -> NominalDiffTime
timeSiceEpoch (Time t) = fromRational (toRational t)


-- | Schedule / run a thread.
--
schedule :: Thread s a -> SimState s a -> ST s (Trace a)
schedule thread@Thread{
           threadId      = tid,
           threadControl = ThreadControl action ctl,
           threadMasking = maskst,
           threadLabel   = tlbl,
           threadStep    = tstep,
           threadVClock  = vClock,
           threadEffect  = effect
         }
         simstate@SimState {
           runqueue,
           threads,
           timers,
           clocks,
           nextVid, nextTmid,
           curTime  = time,
           control
         }
         
  | controlTargets (tid,tstep) control =
      -- The next step is to be delayed according to the
      -- specified schedule. Switch to following the schedule.
      --Debug.trace ("Triggering control: "++show control++"\n") $
      schedule thread simstate{ control = followControl control }
      
  | not $ controlFollows (tid,tstep) control =
      -- the control says this is not the next step to
      -- follow. We should be at the beginning of a step;
      -- we put the present thread to sleep and reschedule
      -- the correct thread.
      assert (effect == mempty) $
      --Debug.trace ("Switching away from "++show (tid,tstep)++"\n"++
      --             "  control = "++show control++"\n") $
      deschedule Sleep thread simstate

  | otherwise =
  assert (invariant (Just thread) simstate) $
  case control of
    ControlFollow (s:_) _ ->
      id --Debug.trace ("Performing action in step "++show s++"\n")
    _ -> id
  $
  case action of

    Return x -> case ctl of
      MainFrame ->
        -- the main thread is done, so we're done
        -- even if other threads are still running
        return $ Trace time tid tlbl EventThreadFinished
               $ traceFinalRacesFound simstate
               $ TraceMainReturn time x (labelledThreads threads)

      ForkFrame -> do
        -- this thread is done
        trace <- deschedule Terminated thread simstate
        return $ Trace time tid tlbl EventThreadFinished trace

      MaskFrame k maskst' ctl' -> do
        -- pop the control stack, restore thread-local state
        let thread' = thread { threadControl = ThreadControl (k x) ctl'
                             , threadMasking = maskst' }
        -- but if we're now unmasked, check for any pending async exceptions
        deschedule Interruptable thread' simstate

      CatchFrame _handler k ctl' -> do
        -- pop the control stack and continue
        let thread' = thread { threadControl = ThreadControl (k x) ctl' }
        schedule thread' simstate

    Throw e -> case unwindControlStack e thread of
      Right thread0 -> do
        -- We found a suitable exception handler, continue with that
        -- We record a step, in case there is no exception handler on replay.
        let thread'  = stepThread thread0
            control' = advanceControl (threadStepId thread0) control
            races'   = updateRacesInSimState thread0 simstate
        trace <- schedule thread' simstate{ races = races', control = control' }
        return (Trace time tid tlbl (EventThrow e) trace)

      Left isMain
        -- We unwound and did not find any suitable exception handler, so we
        -- have an unhandled exception at the top level of the thread.
        | isMain ->
          -- An unhandled exception in the main thread terminates the program
          return (Trace time tid tlbl (EventThrow e) $
                  Trace time tid tlbl (EventThreadUnhandled e) $
                  traceFinalRacesFound simstate $
                  TraceMainException time e (labelledThreads threads))

        | otherwise -> do
          -- An unhandled exception in any other thread terminates the thread
          trace <- deschedule Terminated thread simstate
          return (Trace time tid tlbl (EventThrow e) $
                  Trace time tid tlbl (EventThreadUnhandled e) trace)

    Catch action' handler k -> do
      -- push the failure and success continuations onto the control stack
      let thread' = thread { threadControl = ThreadControl action'
                                               (CatchFrame handler k ctl) }
      schedule thread' simstate

    Evaluate expr k -> do
      mbWHNF <- unsafeIOToST $ try $ evaluate expr
      case mbWHNF of
        Left e -> do
          -- schedule this thread to immediately raise the exception
          let thread' = thread { threadControl = ThreadControl (Throw e) ctl }
          schedule thread' simstate
        Right whnf -> do
          -- continue with the resulting WHNF
          let thread' = thread { threadControl = ThreadControl (k whnf) ctl }
          schedule thread' simstate

    Say msg k -> do
      let thread' = thread { threadControl = ThreadControl k ctl }
      trace <- schedule thread' simstate
      return (Trace time tid tlbl (EventSay msg) trace)

    Output x k -> do
      let thread' = thread { threadControl = ThreadControl k ctl }
      trace <- schedule thread' simstate
      return (Trace time tid tlbl (EventLog x) trace)

    LiftST st k -> do
      x <- strictToLazyST st
      let thread' = thread { threadControl = ThreadControl (k x) ctl,
                             threadEffect  = effect <> liftSTEffect }
      schedule thread' simstate

    GetMonoTime k -> do
      let thread' = thread { threadControl = ThreadControl (k time) ctl }
      schedule thread' simstate

    GetWallTime k -> do
      let clockid  = threadClockId thread
          clockoff = clocks Map.! clockid
          walltime = timeSiceEpoch time `addUTCTime` clockoff
          thread'  = thread { threadControl = ThreadControl (k walltime) ctl }
      schedule thread' simstate

    SetWallTime walltime' k -> do
      let clockid   = threadClockId thread
          clockoff  = clocks Map.! clockid
          walltime  = timeSiceEpoch time `addUTCTime` clockoff
          clockoff' = addUTCTime (diffUTCTime walltime' walltime) clockoff
          thread'   = thread { threadControl = ThreadControl k ctl }
          simstate' = simstate { clocks = Map.insert clockid clockoff' clocks }
      schedule thread' simstate'

    UnshareClock k -> do
      let clockid   = threadClockId thread
          clockoff  = clocks Map.! clockid
          clockid'  = let ThreadId i = tid in ClockId i -- reuse the thread id
          thread'   = thread { threadControl = ThreadControl k ctl
                             , threadClockId = clockid' }
          simstate' = simstate { clocks = Map.insert clockid' clockoff clocks }
      schedule thread' simstate'

    -- we treat negative timers as cancelled ones; for the record we put
    -- `EventTimerCreated` and `EventTimerCancelled` in the trace; This differs
    -- from `GHC.Event` behaviour.
    NewTimeout d k | d < 0 -> do
      let t       = NegativeTimeout nextTmid
          expiry  = d `addTime` time
          thread' = thread { threadControl = ThreadControl (k t) ctl }
      trace <- schedule thread' simstate { nextTmid = succ nextTmid }
      return (Trace time tid tlbl (EventTimerCreated nextTmid nextVid expiry) $
              Trace time tid tlbl (EventTimerCancelled nextTmid) $
              trace)

    NewTimeout d k -> do
      tvar  <- execNewTVar nextVid
                           (Just $ "<<timeout-state " ++ show (unTimeoutId nextTmid) ++ ">>")
                           TimeoutPending
      tvar' <- execNewTVar (succ nextVid)
                           (Just $ "<<timeout " ++ show (unTimeoutId nextTmid) ++ ">>")
                           False
      let expiry  = d `addTime` time
          t       = Timeout tvar tvar' nextTmid
          timers' = PSQ.insert nextTmid expiry (TimerVars tvar tvar') timers
          thread' = thread { threadControl = ThreadControl (k t) ctl }
      trace <- schedule thread' simstate { timers   = timers'
                                         , nextVid  = succ (succ nextVid)
                                         , nextTmid = succ nextTmid }
      return (Trace time tid tlbl (EventTimerCreated nextTmid nextVid expiry) trace)

    -- we do not follow `GHC.Event` behaviour here; updating a timer to the past
    -- effectively cancels it.
    UpdateTimeout (Timeout _tvar _tvar' tmid) d k | d < 0 -> do
      let timers' = PSQ.delete tmid timers
          thread' = thread { threadControl = ThreadControl k ctl }
      trace <- schedule thread' simstate { timers = timers' }
      return (Trace time tid tlbl (EventTimerCancelled tmid) trace)

    UpdateTimeout (Timeout _tvar _tvar' tmid) d k -> do
          -- updating an expired timeout is a noop, so it is safe
          -- to race using a timeout with updating or cancelling it
      let updateTimeout_  Nothing       = ((), Nothing)
          updateTimeout_ (Just (_p, v)) = ((), Just (expiry, v))
          expiry  = d `addTime` time
          timers' = snd (PSQ.alter updateTimeout_ tmid timers)
          thread' = thread { threadControl = ThreadControl k ctl }
      trace <- schedule thread' simstate { timers = timers' }
      return (Trace time tid tlbl (EventTimerUpdated tmid expiry) trace)

    -- updating a negative timer is a no-op, unlike in `GHC.Event`.
    UpdateTimeout (NegativeTimeout _tmid) _d k -> do
      let thread' = thread { threadControl = ThreadControl k ctl }
      schedule thread' simstate

    CancelTimeout (Timeout _tvar _tvar' tmid) k -> do
      let timers' = PSQ.delete tmid timers
          thread' = thread { threadControl = ThreadControl k ctl }
      trace <- schedule thread' simstate { timers = timers' }
      return (Trace time tid tlbl (EventTimerCancelled tmid) trace)

    -- cancelling a negative timer is a no-op
    CancelTimeout (NegativeTimeout _tmid) k -> do
      -- negative timers are promptly removed from the state
      let thread' = thread { threadControl = ThreadControl k ctl }
      schedule thread' simstate

    Fork a k -> do
      let nextTId  = threadNextTId thread
          tid'     = case tid of
                       ThreadId is     -> ThreadId $ is++[nextTId]
                       TestThreadId is
                         | threadRacy thread -> ThreadId     $ is++[nextTId]
                         | otherwise         -> TestThreadId $ is++[nextTId]
          thread'  = thread { threadControl = ThreadControl (k tid') ctl,
                              threadNextTId = nextTId + 1,
                              threadEffect  = effect <> forkEffect tid' }
          thread'' = Thread { threadId      = tid'
                            , threadControl = ThreadControl (runIOSim a)
                                                            ForkFrame
                            , threadBlocked = False
                            , threadDone    = False
                            , threadMasking = threadMasking thread
                            , threadThrowTo = []
                            , threadClockId = threadClockId thread
                            , threadLabel   = Nothing
                            , threadNextTId = 1
                            , threadStep    = 0
                            , threadVClock  = insertVClock tid' 0 vClock
                            , threadEffect  = mempty
                            , threadRacy    = threadRacy thread
                            }
          threads' = Map.insert tid' thread'' threads
      -- A newly forked thread may have a higher priority, so we deschedule this one.
      trace <- deschedule Yield thread'
                 simstate { runqueue = List.insertBy (comparing Down) tid' runqueue
                          , threads  = threads' }
      return (Trace time tid tlbl (EventThreadForked tid') trace)

    Atomically a k -> execAtomically time tid tlbl nextVid (runSTM a) $ \res ->
      case res of
        StmTxCommitted x read written nextVid' -> do
          (wakeup, wokeby) <- threadsUnblockedByWrites written
          mapM_ (\(SomeTVar tvar) -> unblockAllThreadsFromTVar tvar) written
          vClockRead <- lubTVarVClocks read
          let vClock'     = vClock `lubVClock` vClockRead
              effect'     = effect
                         <> readEffects read
                         <> writeEffects written
                         <> wakeupEffects unblocked
              thread'     = thread { threadControl = ThreadControl (k x) ctl,
                                     threadVClock  = vClock',
                                     threadEffect  = effect' }
              (unblocked,
               simstate') = unblockThreads vClock' wakeup simstate
          sequence_ [ modifySTRef (tvarVClock r) (lubVClock vClock') | SomeTVar r <- written ]
          vids <- traverse (\(SomeTVar tvar) -> labelledTVarId tvar) written
              -- We deschedule a thread after a transaction... another may have woken up.
          trace <- deschedule Yield thread' simstate' { nextVid  = nextVid' }
          return $
            Trace time tid tlbl (EventTxCommitted vids [nextVid..pred nextVid']) $
            traceMany
              [ (time, tid', tlbl', EventTxWakeup vids')
              | tid' <- unblocked
              , let tlbl' = lookupThreadLabel tid' threads
              , let Just vids' = Set.toList <$> Map.lookup tid' wokeby ]
              trace

        StmTxAborted read e -> do
          -- schedule this thread to immediately raise the exception
          vClockRead <- lubTVarVClocks read
          let effect' = effect <> readEffects read
              thread' = thread { threadControl = ThreadControl (Throw e) ctl,
                                 threadVClock  = vClock `lubVClock` vClockRead,
                                 threadEffect  = effect' }
          trace <- schedule thread' simstate
          return $ Trace time tid tlbl EventTxAborted trace

        StmTxBlocked read -> do
          mapM_ (\(SomeTVar tvar) -> blockThreadOnTVar tid tvar) read
          vids <- traverse (\(SomeTVar tvar) -> labelledTVarId tvar) read
          vClockRead <- lubTVarVClocks read
          let effect' = effect <> readEffects read
              thread' = thread { threadVClock  = vClock `lubVClock` vClockRead,
                                 threadEffect  = effect' }
          trace <- deschedule Blocked thread' simstate
          return $ Trace time tid tlbl (EventTxBlocked vids) trace

    GetThreadId k -> do
      let thread' = thread { threadControl = ThreadControl (k tid) ctl }
      schedule thread' simstate

    LabelThread tid' l k | tid' == tid -> do
      let thread' = thread { threadControl = ThreadControl k ctl
                           , threadLabel   = Just l }
      schedule thread' simstate

    LabelThread tid' l k -> do
      let thread'  = thread { threadControl = ThreadControl k ctl }
          threads' = Map.adjust (\t -> t { threadLabel = Just l }) tid' threads
      schedule thread' simstate { threads = threads' }

    ExploreRaces k -> do
      let thread'  = thread { threadControl = ThreadControl k ctl
                            , threadRacy    = True }
      schedule thread' simstate

    GetMaskState k -> do
      let thread' = thread { threadControl = ThreadControl (k maskst) ctl }
      schedule thread' simstate

    SetMaskState maskst' action' k -> do
      let thread' = thread { threadControl = ThreadControl
                                               (runIOSim action')
                                               (MaskFrame k maskst ctl)
                           , threadMasking = maskst' }
      case maskst' of
        -- If we're now unmasked then check for any pending async exceptions
        Unmasked -> deschedule Interruptable thread' simstate
        _        -> schedule                 thread' simstate

    ThrowTo e tid' _ | tid' == tid -> do
      -- Throw to ourself is equivalent to a synchronous throw,
      -- and works irrespective of masking state since it does not block.
      let thread' = thread { threadControl = ThreadControl (Throw e) ctl
                           , threadMasking = MaskedInterruptible }
      trace <- schedule thread' simstate
      return (Trace time tid tlbl (EventThrowTo e tid) trace)

    ThrowTo e tid' k -> do
      let thread'    = thread { threadControl = ThreadControl k ctl,
                                threadEffect  = effect <> throwToEffect tid' <> wakeUpEffect,
                                threadVClock  = vClock `lubVClock` vClockTgt }
          (vClockTgt,
           wakeUpEffect,
           willBlock) = (threadVClock t,
                         if threadBlocked t then wakeupEffects [tid'] else mempty,
                         not (threadInterruptible t || threadDone t))
            where Just t = Map.lookup tid' threads
            
      if willBlock
        then do
          -- The target thread has async exceptions masked so we add the
          -- exception and the source thread id to the pending async exceptions.
          let adjustTarget t =
                t { threadThrowTo = (e, Labelled tid tlbl, vClock) : threadThrowTo t }
              threads'       = Map.adjust adjustTarget tid' threads
          trace <- deschedule Blocked thread' simstate { threads = threads' }
          return $ Trace time tid tlbl (EventThrowTo e tid')
                 $ Trace time tid tlbl EventThrowToBlocked
                 $ trace
        else do
          -- The target thread has async exceptions unmasked, or is masked but
          -- is blocked (and all blocking operations are interruptible) then we
          -- raise the exception in that thread immediately. This will either
          -- cause it to terminate or enter an exception handler.
          -- In the meantime the thread masks new async exceptions. This will
          -- be resolved if the thread terminates or if it leaves the exception
          -- handler (when restoring the masking state would trigger the any
          -- new pending async exception).
          let adjustTarget t@Thread{ threadControl = ThreadControl _ ctl',
                                     threadVClock  = vClock' } =
                t { threadControl = ThreadControl (Throw e) ctl'
                  , threadBlocked = False
                  , threadMasking = MaskedInterruptible
                  , threadVClock  = vClock' `lubVClock` vClock }
              simstate'@SimState { threads = threads' }
                         = snd (unblockThreads vClock [tid'] simstate)
              threads''  = Map.adjust adjustTarget tid' threads'
              simstate'' = simstate' { threads = threads'' }

          -- We yield at this point because the target thread may be higher
          -- priority, so this should be a step for race detection.
          trace <- deschedule Yield thread' simstate''
          return $ Trace time tid tlbl (EventThrowTo e tid')
                 $ trace


threadInterruptible :: Thread s a -> Bool
threadInterruptible thread =
    case threadMasking thread of
      Unmasked                 -> True
      MaskedInterruptible
        | threadBlocked thread -> True  -- blocking operations are interruptible
        | otherwise            -> False
      MaskedUninterruptible    -> False

data Deschedule = Yield | Interruptable | Blocked | Terminated | Sleep

deschedule :: Deschedule -> Thread s a -> SimState s a -> ST s (Trace a)

deschedule Yield thread@Thread { threadId     = tid }
                 simstate@SimState{runqueue, threads, control} =

    -- We don't interrupt runnable threads anywhere else.
    -- We do it here by inserting the current thread into the runqueue in priority order.

    let thread'   = stepThread thread
        runqueue' = List.insertBy (comparing Down) tid runqueue
        threads'  = Map.insert tid thread' threads
        control'  = advanceControl (threadStepId thread) control in
    reschedule simstate { runqueue = runqueue', threads  = threads',
                          races    = updateRacesInSimState thread simstate,
                          control  = control' }

deschedule Interruptable thread@Thread {
                           threadId      = tid,
                           threadControl = ThreadControl _ ctl,
                           threadMasking = Unmasked,
                           threadThrowTo = (e, tid', vClock') : etids,
                           threadLabel   = tlbl,
                           threadVClock  = vClock
                         }
                         simstate@SimState{ curTime = time, threads } = do

    -- We're unmasking, but there are pending blocked async exceptions.
    -- So immediately raise the exception and unblock the blocked thread
    -- if possible.
    let thread' = thread { threadControl = ThreadControl (Throw e) ctl
                         , threadMasking = MaskedInterruptible
                         , threadThrowTo = etids
                         , threadVClock  = vClock `lubVClock` vClock' }
        (unblocked,
         simstate') = unblockThreads vClock [l_labelled tid'] simstate
    -- the thread is stepped when we Yield
    trace <- deschedule Yield thread' simstate'
    return $ Trace time tid tlbl (EventThrowToUnmasked tid')
           $ traceMany [ (time, tid'', tlbl'', EventThrowToWakeup)
                       | tid'' <- unblocked
                       , let tlbl'' = lookupThreadLabel tid'' threads ]
             trace

deschedule Interruptable thread simstate@SimState{ control } =
    -- Either masked or unmasked but no pending async exceptions.
    -- Either way, just carry on.
    -- Record a step, though, in case on replay there is an async exception.
    let thread' = stepThread thread in 
    schedule thread'
             simstate{ races   = updateRacesInSimState thread simstate,
                       control = advanceControl (threadStepId thread) control }

deschedule Blocked thread@Thread { threadThrowTo = _ : _
                                 , threadMasking = maskst } simstate
    | maskst /= MaskedUninterruptible =
    -- We're doing a blocking operation, which is an interrupt point even if
    -- we have async exceptions masked, and there are pending blocked async
    -- exceptions. So immediately raise the exception and unblock the blocked
    -- thread if possible.
    deschedule Interruptable thread { threadMasking = Unmasked } simstate

deschedule Blocked thread simstate@SimState{threads, control} =
    let thread'  = stepThread $ thread { threadBlocked = True }
        threads' = Map.insert (threadId thread') thread' threads in
    reschedule simstate { threads = threads',
                          races   = updateRacesInSimState thread simstate,
                          control = advanceControl (threadStepId thread) control }

deschedule Terminated thread@Thread { threadId = tid, threadVClock = vClock }
                      simstate@SimState{ curTime = time, control } = do
    -- This thread is done. If there are other threads blocked in a
    -- ThrowTo targeted at this thread then we can wake them up now.
    let thread'     = stepThread $ thread{ threadDone = True }
        wakeup      = map (\(_,tid',_) -> l_labelled tid') (reverse (threadThrowTo thread))
        (unblocked,
         simstate'@SimState{threads}) =
                      unblockThreads vClock wakeup simstate
        threads'    = Map.insert tid thread' threads
    -- We must keep terminated threads in the state to preserve their vector clocks,
    -- which matters when other threads throwTo them.
    trace <- reschedule simstate' { races = threadTerminatesRaces tid $
                                              updateRacesInSimState thread simstate,
                                    control = advanceControl (threadStepId thread) control,
                                    threads = threads' }
    return $ traceMany
               [ (time, tid', tlbl', EventThrowToWakeup)
               | tid' <- unblocked
               , let tlbl' = lookupThreadLabel tid' threads ]
               trace

deschedule Sleep thread@Thread { threadId = tid }
                 simstate@SimState{runqueue, threads} =

    -- Schedule control says we should run a different thread. Put
    -- this one to sleep without recording a step.

    let runqueue' = List.insertBy (comparing Down) tid runqueue
        threads'  = Map.insert tid thread threads in
    reschedule simstate { runqueue = runqueue', threads  = threads' }


-- Choose the next thread to run.
reschedule :: SimState s a -> ST s (Trace a)

-- If we are following a controlled schedule, just do that.
reschedule simstate@SimState{ runqueue, threads,
                              control=control@(ControlFollow ((tid,tstep):_) _)
                              } =
    if not (tid `elem` runqueue) then
      error ("Can't follow "++show control++"\n"++
             "  tid: "++show tid++"\n"++
             "  tstep: "++show tstep++"\n"++
             "  runqueue: "++show runqueue++"\n") else
    assert (tid `elem` runqueue) $
    assert (tid `Map.member` threads) $
    assert (invariant Nothing simstate) $  
    let thread = threads Map.! tid in
    assert (threadId thread == tid) $
    --assert (threadStep thread == tstep) $
    if threadStep thread /= tstep then
      error $ "Thread step out of sync\n"
           ++ "  runqueue:    "++show runqueue++"\n"
           ++ "  follows:     "++show tid++", step "++show tstep++"\n"
           ++ "  actual step: "++show (threadStep thread)++"\n"
           ++ "Thread:\n" ++ show thread ++ "\n"
    else
    schedule thread simstate { runqueue = List.delete tid runqueue
                             , threads  = Map.delete tid threads }

-- When there is no current running thread but the runqueue is non-empty then
-- schedule the next one to run. 
reschedule simstate@SimState{ runqueue = tid:runqueue', threads } =
    assert (invariant Nothing simstate) $

    let thread = threads Map.! tid in
    schedule thread simstate { runqueue = runqueue'
                             , threads  = Map.delete tid threads }

-- But when there are no runnable threads, we advance the time to the next
-- timer event, or stop.
reschedule simstate@SimState{ runqueue = [], threads, timers, curTime = time, races } =
    assert (invariant Nothing simstate) $

    -- time is moving on
    --Debug.trace ("Rescheduling at "++show time++", "++
      --show (length (concatMap stepInfoRaces (activeRaces races++completeRaces races)))++" races") $

    -- important to get all events that expire at this time
    case removeMinimums timers of
      Nothing -> return (traceFinalRacesFound simstate $
                         TraceDeadlock time (labelledThreads threads))

      Just (tmids, time', fired, timers') -> assert (time' >= time) $ do

        -- Reuse the STM functionality here to write all the timer TVars.
        -- Simplify to a special case that only reads and writes TVars.
        written <- execAtomically' (runSTM $ mapM_ timeoutAction fired)
        (wakeup, wokeby) <- threadsUnblockedByWrites written
        mapM_ (\(SomeTVar tvar) -> unblockAllThreadsFromTVar tvar) written

        -- TODO: the vector clock below cannot be right, can it?
        let (unblocked,
             simstate') = unblockThreads bottomVClock wakeup simstate
            -- all open races will be completed and reported at this time
            simstate''  = simstate'{ races = noRaces }
        trace <- reschedule simstate'' { curTime = time'
                                       , timers  = timers' }
        let traceEntries =
                     [ (time', ThreadId [-1], Just "timer", EventTimerExpired tmid)
                     | tmid <- tmids ]
                  ++ [ (time', tid', tlbl', EventTxWakeup vids)
                     | tid' <- unblocked
                     , let tlbl' = lookupThreadLabel tid' threads
                     , let Just vids = Set.toList <$> Map.lookup tid' wokeby ]
        return $
          traceFinalRacesFound simstate $
          traceMany traceEntries trace
  where
    timeoutAction (TimerVars var bvar) = do
      x <- readTVar var
      case x of
        TimeoutPending   -> writeTVar var  TimeoutFired
                         >> writeTVar bvar True
        TimeoutFired     -> error "MonadTimer(Sim): invariant violation"
        TimeoutCancelled -> return ()

unblockThreads :: VectorClock -> [ThreadId] -> SimState s a -> ([ThreadId], SimState s a)
unblockThreads vClock wakeup simstate@SimState {runqueue, threads} =
    -- To preserve our invariants (that threadBlocked is correct)
    -- we update the runqueue and threads together here
    (unblocked, simstate {
                  runqueue = foldr (List.insertBy (comparing Down)) runqueue unblocked,
                  threads  = threads'
                })
  where
    -- can only unblock if the thread exists and is blocked (not running)
    unblocked = [ tid
                | tid <- wakeup
                , case Map.lookup tid threads of
                       Just Thread { threadDone    = True } -> False
                       Just Thread { threadBlocked = True } -> True
                       _                                    -> False
                ]
    -- and in which case we mark them as now running
    threads'  = List.foldl'
                  (flip (Map.adjust
                    (\t -> t { threadBlocked = False,
                               threadVClock = vClock `lubVClock` threadVClock t })))
                  threads unblocked


-- | Iterate through the control stack to find an enclosing exception handler
-- of the right type, or unwind all the way to the top level for the thread.
--
-- Also return if it's the main thread or a forked thread since we handle the
-- cases differently.
--
unwindControlStack :: forall s a.
                      SomeException
                   -> Thread s a
                   -> Either Bool (Thread s a)
unwindControlStack e thread =
    case threadControl thread of
      ThreadControl _ ctl -> unwind (threadMasking thread) ctl
  where
    unwind :: forall s' c. MaskingState
           -> ControlStack s' c a -> Either Bool (Thread s' a)
    unwind _  MainFrame                 = Left True
    unwind _  ForkFrame                 = Left False
    unwind _ (MaskFrame _k maskst' ctl) = unwind maskst' ctl

    unwind maskst (CatchFrame handler k ctl) =
      case fromException e of
        -- not the right type, unwind to the next containing handler
        Nothing -> unwind maskst ctl

        -- Ok! We will be able to continue the thread with the handler
        -- followed by the continuation after the catch
        Just e' -> Right thread {
                      -- As per async exception rules, the handler is run masked
                     threadControl = ThreadControl (handler e')
                                                   (MaskFrame k maskst ctl),
                     threadMasking = max maskst MaskedInterruptible
                   }


removeMinimums :: (Ord k, Ord p)
               => OrdPSQ k p a
               -> Maybe ([k], p, [a], OrdPSQ k p a)
removeMinimums = \psq ->
    case PSQ.minView psq of
      Nothing              -> Nothing
      Just (k, p, x, psq') -> Just (collectAll [k] p [x] psq')
  where
    collectAll ks p xs psq =
      case PSQ.minView psq of
        Just (k, p', x, psq')
          | p == p' -> collectAll (k:ks) p (x:xs) psq'
        _           -> (reverse ks, p, reverse xs, psq)

traceMany :: [(Time, ThreadId, Maybe ThreadLabel, TraceEvent)]
          -> Trace a -> Trace a
traceMany []                      trace = trace
traceMany ((time, tid, tlbl, event):ts) trace =
    Trace time tid tlbl event (traceMany ts trace)

lookupThreadLabel :: ThreadId -> Map ThreadId (Thread s a) -> Maybe ThreadLabel
lookupThreadLabel tid threads = join (threadLabel <$> Map.lookup tid threads)


-- | The most general method of running 'IOSim' is in 'ST' monad.  One can
-- recover failures or the result from 'Trace' with 'traceResult', or access
-- 'TraceEvent's generated by the computation with 'traceEvents'.  A slightly
-- more convenient way is exposed by 'runSimTrace'.
--
runSimTraceST :: forall s a. IOSim s a -> ST s (Trace a)
runSimTraceST mainAction = controlSimTraceST ControlDefault mainAction

controlSimTraceST :: ScheduleControl -> IOSim s a -> ST s (Trace a)
controlSimTraceST control mainAction =
  schedule mainThread initialState{ control = control, control0 = control }
  where
    mainThread =
      Thread {
        threadId      = TestThreadId [],
        threadControl = ThreadControl (runIOSim mainAction) MainFrame,
        threadBlocked = False,
        threadDone    = False,
        threadMasking = Unmasked,
        threadThrowTo = [],
        threadClockId = ClockId [],
        threadLabel   = Just "main",
        threadNextTId = 1,
        threadStep    = 0,
        threadVClock  = insertVClock (TestThreadId []) 0 bottomVClock,
        threadEffect  = mempty,
        threadRacy    = False
      }


--
-- Executing STM Transactions
--

data TVar s a = TVar {

       -- | The identifier of this var.
       --
       tvarId      :: !TVarId,

       -- | Label.
       tvarLabel   :: !(STRef s (Maybe TVarLabel)),

       -- | The var's current value
       --
       tvarCurrent :: !(STRef s a),

       -- | A stack of undo values. This is only used while executing a
       -- transaction.
       --
       tvarUndo    :: !(STRef s [a]),

       -- | Thread Ids of threads blocked on a read of this var. It is
       -- represented in reverse order of thread wakeup, without duplicates.
       --
       -- To avoid duplicates efficiently, the operations rely on a copy of the
       -- thread Ids represented as a set.
       --
       tvarBlocked :: !(STRef s ([ThreadId], Set ThreadId)),

       -- | The vector clock of the current value.
       --
       tvarVClock :: !(STRef s VectorClock)
     }

instance Eq (TVar s a) where
    (==) = on (==) tvarId

data StmTxResult s a =
       -- | A committed transaction reports the vars that were written (in order
       -- of first write) so that the scheduler can unblock other threads that
       -- were blocked in STM transactions that read any of these vars.
       --
       -- It reports the vars that were read, so we can update vector clocks
       -- appropriately.
       --
       -- It also includes the updated TVarId name supply.
       --
       StmTxCommitted a [SomeTVar s] [SomeTVar s] TVarId -- updated TVarId name supply

       -- | A blocked transaction reports the vars that were read so that the
       -- scheduler can block the thread on those vars.
       --
     | StmTxBlocked  [SomeTVar s]

       -- | An aborted transaction reports the vars that were read so that the
       -- vector clock can be updated.
       --
     | StmTxAborted  [SomeTVar s] SomeException

data SomeTVar s where
  SomeTVar :: !(TVar s a) -> SomeTVar s

data StmStack s b a where
  -- | Executing in the context of a top level 'atomically'.
  AtomicallyFrame  :: StmStack s a a

  -- | Executing in the context of the /left/ hand side of an 'orElse'
  OrElseLeftFrame  :: StmA s a                -- orElse right alternative
                   -> (a -> StmA s b)         -- subsequent continuation
                   -> Map TVarId (SomeTVar s) -- saved written vars set
                   -> [SomeTVar s]            -- saved written vars list
                   -> StmStack s b c
                   -> StmStack s a c

  -- | Executing in the context of the /right/ hand side of an 'orElse'
  OrElseRightFrame :: (a -> StmA s b)         -- subsequent continuation
                   -> Map TVarId (SomeTVar s) -- saved written vars set
                   -> [SomeTVar s]            -- saved written vars list
                   -> StmStack s b c
                   -> StmStack s a c

execAtomically :: forall s a c.
                  Time
               -> ThreadId
               -> Maybe ThreadLabel
               -> TVarId
               -> StmA s a
               -> (StmTxResult s a -> ST s (Trace c))
               -> ST s (Trace c)
execAtomically time tid tlbl nextVid0 action0 k0 =
    go AtomicallyFrame Map.empty Map.empty [] nextVid0 action0
  where
    go :: forall b.
          StmStack s b a
       -> Map TVarId (SomeTVar s)  -- set of vars read
       -> Map TVarId (SomeTVar s)  -- set of vars written
       -> [SomeTVar s]             -- vars written in order (no dups)
       -> TVarId                   -- var fresh name supply
       -> StmA s b
       -> ST s (Trace c)
    go ctl !read !written writtenSeq !nextVid action = assert localInvariant $
                                                       case action of
      ReturnStm x -> case ctl of
        AtomicallyFrame -> do
          -- Commit each TVar
          traverse_ (\(SomeTVar tvar) -> do
                        commitTVar tvar
                        -- Also assert the data invariant that outside a tx
                        -- the undo stack is empty:
                        undos <- readTVarUndos tvar
                        assert (null undos) $ return ()
                    ) written

          -- Return the vars written, so readers can be unblocked
          k0 $ StmTxCommitted x (Map.elems read)
                                (reverse writtenSeq) nextVid

        OrElseLeftFrame _b k writtenOuter writtenOuterSeq ctl' -> do
          -- Commit the TVars written in this sub-transaction that are also
          -- in the written set of the outer transaction
          traverse_ (\(SomeTVar tvar) -> commitTVar tvar)
                    (Map.intersection written writtenOuter)
          -- Merge the written set of the inner with the outer
          let written'    = Map.union written writtenOuter
              writtenSeq' = filter (\(SomeTVar tvar) ->
                                      tvarId tvar `Map.notMember` writtenOuter)
                                    writtenSeq
                         ++ writtenOuterSeq
          -- Skip the orElse right hand and continue with the k continuation
          go ctl' read written' writtenSeq' nextVid (k x)

        OrElseRightFrame k writtenOuter writtenOuterSeq ctl' -> do
          -- Commit the TVars written in this sub-transaction that are also
          -- in the written set of the outer transaction
          traverse_ (\(SomeTVar tvar) -> commitTVar tvar)
                    (Map.intersection written writtenOuter)
          -- Merge the written set of the inner with the outer
          let written'    = Map.union written writtenOuter
              writtenSeq' = filter (\(SomeTVar tvar) ->
                                      tvarId tvar `Map.notMember` writtenOuter)
                                    writtenSeq
                         ++ writtenOuterSeq
          -- Continue with the k continuation
          go ctl' read written' writtenSeq' nextVid (k x)

      ThrowStm e -> do
        -- Revert all the TVar writes
        traverse_ (\(SomeTVar tvar) -> revertTVar tvar) written
        k0 $ StmTxAborted (Map.elems read) (toException e)

      Retry -> case ctl of
        AtomicallyFrame -> do
          -- Revert all the TVar writes
          traverse_ (\(SomeTVar tvar) -> revertTVar tvar) written
          -- Return vars read, so the thread can block on them
          k0 $ StmTxBlocked (Map.elems read)

        OrElseLeftFrame b k writtenOuter writtenOuterSeq ctl' -> do
          -- Revert all the TVar writes within this orElse
          traverse_ (\(SomeTVar tvar) -> revertTVar tvar) written
          -- Execute the orElse right hand with an empty written set
          let ctl'' = OrElseRightFrame k writtenOuter writtenOuterSeq ctl'
          go ctl'' read Map.empty [] nextVid b

        OrElseRightFrame _k writtenOuter writtenOuterSeq ctl' -> do
          -- Revert all the TVar writes within this orElse branch
          traverse_ (\(SomeTVar tvar) -> revertTVar tvar) written
          -- Skip the continuation and propagate the retry into the outer frame
          -- using the written set for the outer frame
          go ctl' read writtenOuter writtenOuterSeq nextVid Retry

      OrElse a b k -> do
        -- Execute the left side in a new frame with an empty written set
        let ctl' = OrElseLeftFrame b k written writtenSeq ctl
        go ctl' read Map.empty [] nextVid a

      NewTVar !mbLabel x k -> do
        v <- execNewTVar nextVid mbLabel x
        -- record a write to the TVar so we know to update its VClock
        let written' = Map.insert (tvarId v) (SomeTVar v) written
        -- save the value: it will be committed or reverted
        saveTVar v
        go ctl read written' (SomeTVar v : writtenSeq) (succ nextVid) (k v)

      LabelTVar !label tvar k -> do
        writeSTRef (tvarLabel tvar) $! (Just label)
        go ctl read written writtenSeq nextVid k

      ReadTVar v k
        | tvarId v `Map.member` read || tvarId v `Map.member` written -> do
            x <- execReadTVar v
            go ctl read written writtenSeq nextVid (k x)
        | otherwise -> do
            x <- execReadTVar v
            let read' = Map.insert (tvarId v) (SomeTVar v) read
            go ctl read' written writtenSeq nextVid (k x)

      WriteTVar v x k
        | tvarId v `Map.member` written -> do
            execWriteTVar v x
            go ctl read written writtenSeq nextVid k
        | otherwise -> do
            saveTVar v
            execWriteTVar v x
            let written' = Map.insert (tvarId v) (SomeTVar v) written
            go ctl read written' (SomeTVar v : writtenSeq) nextVid k

      SayStm msg k -> do
        trace <- go ctl read written writtenSeq nextVid k
        return $ Trace time tid tlbl (EventSay msg) trace

      OutputStm x k -> do
        trace <- go ctl read written writtenSeq nextVid k
        return $ Trace time tid tlbl (EventLog x) trace

      where
        localInvariant =
            Map.keysSet written
         == Set.fromList [ tvarId tvar | SomeTVar tvar <- writtenSeq ]


-- | Special case of 'execAtomically' supporting only var reads and writes
--
execAtomically' :: StmA s () -> ST s [SomeTVar s]
execAtomically' = go Map.empty
  where
    go :: Map TVarId (SomeTVar s)  -- set of vars written
       -> StmA s ()
       -> ST s [SomeTVar s]
    go !written action = case action of
      ReturnStm () -> do
        traverse_ (\(SomeTVar tvar) -> commitTVar tvar) written
        return (Map.elems written)
      ReadTVar v k  -> do
        x <- execReadTVar v
        go written (k x)
      WriteTVar v x k
        | tvarId v `Map.member` written -> do
            execWriteTVar v x
            go written k
        | otherwise -> do
            saveTVar v
            execWriteTVar v x
            let written' = Map.insert (tvarId v) (SomeTVar v) written
            go written' k
      _ -> error "execAtomically': only for special case of reads and writes"


execNewTVar :: TVarId -> Maybe String -> a -> ST s (TVar s a)
execNewTVar nextVid !mbLabel x = do
    tvarLabel   <- newSTRef mbLabel
    tvarCurrent <- newSTRef x
    tvarUndo    <- newSTRef []
    tvarBlocked <- newSTRef ([], Set.empty)
    tvarVClock  <- newSTRef bottomVClock
    return TVar {tvarId = nextVid, tvarLabel,
                 tvarCurrent, tvarUndo, tvarBlocked, tvarVClock}

execReadTVar :: TVar s a -> ST s a
execReadTVar TVar{tvarCurrent} = readSTRef tvarCurrent

execWriteTVar :: TVar s a -> a -> ST s ()
execWriteTVar TVar{tvarCurrent} = writeSTRef tvarCurrent

saveTVar :: TVar s a -> ST s ()
saveTVar TVar{tvarCurrent, tvarUndo} = do
    -- push the current value onto the undo stack
    v  <- readSTRef tvarCurrent
    vs <- readSTRef tvarUndo
    writeSTRef tvarUndo (v:vs)

revertTVar :: TVar s a -> ST s ()
revertTVar TVar{tvarCurrent, tvarUndo} = do
    -- pop the undo stack, and revert the current value
    (v:vs) <- readSTRef tvarUndo
    writeSTRef tvarCurrent v
    writeSTRef tvarUndo    vs

commitTVar :: TVar s a -> ST s ()
commitTVar TVar{tvarUndo} = do
    -- pop the undo stack, leaving the current value unchanged
    (_:vs) <- readSTRef tvarUndo
    writeSTRef tvarUndo vs

readTVarUndos :: TVar s a -> ST s [a]
readTVarUndos TVar{tvarUndo} = readSTRef tvarUndo

lubTVarVClocks :: [SomeTVar s] -> ST s VectorClock
lubTVarVClocks tvars =
  foldr lubVClock bottomVClock <$>
    sequence [readSTRef (tvarVClock r) | SomeTVar r <- tvars]

--
-- Blocking and unblocking on TVars
--

readTVarBlockedThreads :: TVar s a -> ST s [ThreadId]
readTVarBlockedThreads TVar{tvarBlocked} = fst <$> readSTRef tvarBlocked

blockThreadOnTVar :: ThreadId -> TVar s a -> ST s ()
blockThreadOnTVar tid TVar{tvarBlocked} = do
    (tids, tidsSet) <- readSTRef tvarBlocked
    when (tid `Set.notMember` tidsSet) $ do
      let !tids'    = tid : tids
          !tidsSet' = Set.insert tid tidsSet
      writeSTRef tvarBlocked (tids', tidsSet')

unblockAllThreadsFromTVar :: TVar s a -> ST s ()
unblockAllThreadsFromTVar TVar{tvarBlocked} = do
    writeSTRef tvarBlocked ([], Set.empty)

-- | For each TVar written to in a transaction (in order) collect the threads
-- that blocked on each one (in order).
--
-- Also, for logging purposes, return an association between the threads and
-- the var writes that woke them.
--
threadsUnblockedByWrites :: [SomeTVar s]
                         -> ST s ([ThreadId], Map ThreadId (Set (Labelled TVarId)))
threadsUnblockedByWrites written = do
  tidss <- sequence
             [ (,) <$> labelledTVarId tvar <*> readTVarBlockedThreads tvar
             | SomeTVar tvar <- written ]
  -- Threads to wake up, in wake up order, annotated with the vars written that
  -- caused the unblocking.
  -- We reverse the individual lists because the tvarBlocked is used as a stack
  -- so it is in order of last written, LIFO, and we want FIFO behaviour.
  let wakeup = ordNub [ tid | (_vid, tids) <- tidss, tid <- reverse tids ]
      wokeby = Map.fromListWith Set.union
                                [ (tid, Set.singleton vid)
                                | (vid, tids) <- tidss
                                , tid <- tids ]
  return (wakeup, wokeby)

ordNub :: Ord a => [a] -> [a]
ordNub = go Set.empty
  where
    go !_ [] = []
    go !s (x:xs)
      | x `Set.member` s = go s xs
      | otherwise        = x : go (Set.insert x s) xs

-- Effects

data Effect = Effect {
    effectReads  :: !(Set TVarId),
    effectWrites :: !(Set TVarId),
    effectForks  :: !(Set ThreadId),
    effectLiftST :: !Bool,
    effectThrows :: ![ThreadId],
    effectWakeup :: ![ThreadId]
  }
  deriving (Eq, Show)

instance Semigroup Effect where
  Effect r w s b ts wu <> Effect r' w' s' b' ts' wu' =
    Effect (r<>r') (w<>w') (s<>s') (b||b') (ts++ts') (wu++wu')

instance Monoid Effect where
  mempty = Effect Set.empty Set.empty Set.empty False [] []

readEffect :: SomeTVar s -> Effect
readEffect r = mempty{effectReads = Set.singleton $ someTvarId r }

readEffects :: [SomeTVar s] -> Effect
readEffects rs = mempty{effectReads = Set.fromList (map someTvarId rs)}

writeEffect :: SomeTVar s -> Effect
writeEffect r = mempty{effectWrites = Set.singleton $ someTvarId r }

writeEffects :: [SomeTVar s] -> Effect
writeEffects rs = mempty{effectWrites = Set.fromList (map someTvarId rs)}

forkEffect :: ThreadId -> Effect
forkEffect tid = mempty{effectForks = Set.singleton $ tid}

liftSTEffect :: Effect
liftSTEffect = mempty{ effectLiftST = True }

throwToEffect :: ThreadId -> Effect
throwToEffect tid = mempty{ effectThrows = [tid] }

wakeupEffects :: [ThreadId] -> Effect
wakeupEffects tids = mempty{effectWakeup = tids}

someTvarId :: SomeTVar s -> TVarId
someTvarId (SomeTVar r) = tvarId r

onlyReadEffect :: Effect -> Bool
onlyReadEffect e@Effect { effectReads } = e == mempty { effectReads }

racingEffects :: Effect -> Effect -> Bool
racingEffects e e' =
      (effectLiftST e  && racesWithLiftST e')
   || (effectLiftST e' && racesWithLiftST e )
   || (not $ null $ effectThrows e `List.intersect` effectThrows e')
   || (not $ effectReads  e `Set.disjoint` effectWrites e'
          && effectWrites e `Set.disjoint` effectReads  e'
          && effectWrites e `Set.disjoint` effectWrites e')
  where racesWithLiftST eff =
             effectLiftST eff
          || not (Set.null (effectReads eff) && Set.null (effectWrites eff))
  
-- Steps

data Step = Step {
    stepThreadId :: !ThreadId,
    stepStep     :: !Int,
    stepEffect   :: !Effect,
    stepVClock   :: !VectorClock
  }
  deriving Show

-- steps race if they can be reordered with a possibly different outcome
racingSteps :: Step -> Step -> Bool
racingSteps s s' =
     stepThreadId s /= stepThreadId s'
  && not (stepThreadId s' `elem` effectWakeup (stepEffect s))
  && (racingEffects (stepEffect s) (stepEffect s')
   || throwsTo s s'
   || throwsTo s' s)
  where throwsTo s1 s2 =
             stepThreadId s1 `elem` effectThrows (stepEffect s2)
          && stepEffect s1 /= mempty

currentStep :: Thread s a -> Step
currentStep Thread { threadId     = tid,
                     threadStep   = tstep,
                     threadEffect = teffect,
                     threadVClock = vClock
                   } =
  Step { stepThreadId = tid,
         stepStep     = tstep,
         stepEffect   = teffect,
         stepVClock   = vClock
       }

stepThread :: Thread s a -> Thread s a
stepThread thread@Thread { threadId     = tid,
                           threadStep   = tstep,
                           threadVClock = vClock } =
  thread { threadStep   = tstep+1,
           threadEffect = mempty,
           threadVClock = insertVClock tid (tstep+1) vClock
         }

-- As we run a simulation, we collect info about each previous step
data StepInfo = StepInfo {
    stepInfoStep       :: Step,
    -- Control information when we reached this step
    stepInfoControl    :: ScheduleControl,
    -- threads that are still concurrent with this step
    stepInfoConcurrent :: Set ThreadId,
    -- steps following this one that did not happen after it
    -- (in reverse order)
    stepInfoNonDep     :: [Step],
    -- later steps that race with this one
    stepInfoRaces      :: [Step]
  }
  deriving Show

data Races = Races { -- These steps may still race with future steps
                     activeRaces   :: ![StepInfo],
                     -- These steps cannot be concurrent with future steps
                     completeRaces :: ![StepInfo]
                   }
  deriving Show

noRaces :: Races
noRaces = Races [] []

updateRacesInSimState :: Thread s a -> SimState s a -> Races
updateRacesInSimState thread SimState{ control, threads, races } =
  traceRaces $
  updateRaces (currentStep thread)
              (threadBlocked thread)
              control
              (Map.keysSet (Map.filter (not . threadDone) threads))
              races

-- We take care that steps can only race against threads in their
-- concurrent set. When this becomes empty, a step can be retired into
-- the "complete" category, but only if there are some steps racing
-- with it.
updateRaces :: Step -> Bool -> ScheduleControl -> Set ThreadId -> Races -> Races
updateRaces newStep@Step{ stepThreadId = tid, stepEffect = newEffect }
            blocking
            control
            newConcurrent0
            races@Races{ activeRaces } =
  let -- a new step cannot race with any threads that it just woke up
      newConcurrent = foldr Set.delete newConcurrent0 (effectWakeup newEffect)
      new | isTestThreadId tid     = []  -- test threads do not race
          | Set.null newConcurrent = []  -- cannot race with anything
          | justBlocking           = []  -- no need to defer a blocking transaction
          | otherwise              =
              [StepInfo { stepInfoStep       = newStep,
                          stepInfoControl    = control,
                          stepInfoConcurrent = newConcurrent,
                          stepInfoNonDep     = [],
                          stepInfoRaces      = []
                        }]
      justBlocking = blocking && onlyReadEffect newEffect
      updateActive =
        [ -- if this step depends on the previous step, then any threads
          -- that it wakes up become dependent also.
          let lessConcurrent = foldr Set.delete concurrent (effectWakeup newEffect) in
          if tid `elem` concurrent then
            let (nondep', concurrent')
                  | hbfStep (stepThreadId step) (stepStep step) (stepVClock newStep) =
                    (nondep, Set.delete tid lessConcurrent)
                  | otherwise =
                    (newStep : nondep, concurrent)
                -- Here we record discovered races.
                -- We only record a race if we are following the default schedule,
                -- to avoid finding the same race in different parts of the search space.
                -- We record only the first race with each thread
                stepRaces' | control == ControlDefault &&
                             tid `notElem` map stepThreadId stepRaces &&
                             not (isTestThreadId tid) &&
                             racingSteps step newStep = newStep : stepRaces
                           | otherwise                = stepRaces
            in stepInfo { stepInfoConcurrent = effectForks newEffect `Set.union` concurrent',
                          stepInfoNonDep     = nondep',
                          stepInfoRaces      = stepRaces'
                        }
          else stepInfo { stepInfoConcurrent = lessConcurrent }
        | stepInfo@StepInfo { stepInfoStep       = step,
                              stepInfoConcurrent = concurrent,
                              stepInfoNonDep     = nondep,
                              stepInfoRaces      = stepRaces
                            }
            <- activeRaces ]
  in normalizeRaces $ races { activeRaces = new ++ updateActive }

-- When a thread terminates, we remove it from the concurrent thread
-- sets of active races.

threadTerminatesRaces :: ThreadId -> Races -> Races
threadTerminatesRaces tid races@Races{ activeRaces } =
  let activeRaces' = [ s{stepInfoConcurrent = Set.delete tid stepInfoConcurrent}
                     | s@StepInfo{ stepInfoConcurrent } <- activeRaces ]
  in normalizeRaces $ races{ activeRaces = activeRaces' }

normalizeRaces :: Races -> Races
normalizeRaces Races{ activeRaces, completeRaces } =
  let activeRaces' = filter (not . null. stepInfoConcurrent) activeRaces
      completeRaces' = filter (not . null. stepInfoRaces)
                         (filter (null . stepInfoConcurrent) activeRaces)
                    ++ completeRaces
  in Races{ activeRaces = activeRaces', completeRaces = completeRaces' }
  
-- We assume that steps do not race with later steps after a quiescent
-- period. Quiescent periods end when simulated time advances, thus we
-- are assuming here that all work is completed before a timer
-- triggers.

quiescentRacesInSimState :: SimState s a -> SimState s a
quiescentRacesInSimState simstate@SimState{ races } =
  simstate{ races = quiescentRaces races }
  
quiescentRaces :: Races -> Races
quiescentRaces Races{ activeRaces, completeRaces } =
  Races{ activeRaces = [],
         completeRaces = [s{stepInfoConcurrent = Set.empty} |
                          s <- activeRaces,
                          not (null (stepInfoRaces s))] ++
                         completeRaces }

traceRaces :: Races -> Races
traceRaces r@Races{activeRaces,completeRaces} =
  r
--  Debug.trace ("Tracking "++show (length (concatMap stepInfoRaces activeRaces)) ++" races") r

-- Schedule modifications

data ScheduleMod = ScheduleMod{
    scheduleModTarget    :: StepId,   -- when we reach this step
    scheduleModControl   :: ScheduleControl,
                                      -- which happens with this control
    scheduleModInsertion :: [StepId]  -- we should instead perform this sequence
                                      -- this *includes* the target step,
                                      -- not necessarily as the last step.
  }
  deriving (Eq, Ord)

instance Show ScheduleMod where
  showsPrec d (ScheduleMod tgt ctrl insertion) =
    showParen (d>10) $
      showString "ScheduleMod " .
      showsPrec 11 tgt .
      showSpace .
      showsPrec 11 ctrl .
      showSpace .
      showsPrec 11 insertion

type StepId = (ThreadId,Int)

stepStepId :: Step -> (ThreadId, Int)
stepStepId Step{ stepThreadId = tid, stepStep = n } = (tid,n)

threadStepId :: Thread s a -> (ThreadId, Int)
threadStepId Thread{ threadId, threadStep } = (threadId, threadStep)

stepInfoToScheduleMods :: StepInfo -> [ScheduleMod]
stepInfoToScheduleMods
  StepInfo{ stepInfoStep    = step,
            stepInfoControl = control,
            stepInfoNonDep  = nondep,
            stepInfoRaces   = races
          } =
  -- It is actually possible for a later step that races with an earlier one
  -- not to *depend* on it in a happens-before sense. But we don't want to try
  -- to follow any steps *after* the later one.
  [ ScheduleMod (stepStepId step)
                control
                (takeWhile (/=stepStepId step')
                   (map stepStepId (reverse nondep))
                   ++ [stepStepId step'])
                   -- It should be unnecessary to include the delayed step in the insertion,
                   -- since the default scheduling should run it anyway. Removing it may
                   -- help avoid redundant schedules.
                   -- ++ [stepStepId step])
  | step' <- races ]

traceFinalRacesFound :: SimState s a -> Trace a -> Trace a
traceFinalRacesFound simstate@SimState{ control0 = control } =
  TraceRacesFound [extendScheduleControl control m | m <- scheduleMods]
  where SimState{ races } =
          quiescentRacesInSimState simstate
        scheduleMods =
          concatMap stepInfoToScheduleMods $ completeRaces races


-- Schedule control

data ScheduleControl = ControlDefault
                     | ControlAwait [ScheduleMod]
                     | ControlFollow [StepId] [ScheduleMod]
  deriving (Eq, Ord, Show)

controlTargets :: StepId -> ScheduleControl -> Bool
controlTargets stepId
               (ControlAwait (ScheduleMod{ scheduleModTarget }:_)) =
  stepId == scheduleModTarget
controlTargets _stepId _ = False

controlFollows :: StepId -> ScheduleControl -> Bool
controlFollows _stepId ControlDefault               = True
controlFollows stepId (ControlFollow (stepId':_) _) = stepId == stepId'
controlFollows stepId (ControlAwait (smod:_))       =
  stepId /= scheduleModTarget smod

advanceControl :: (ThreadId, Int) -> ScheduleControl -> ScheduleControl
advanceControl (tid,step) (ControlFollow ((tid',step'):sids) tgts)
  | tid /= tid' =
      -- we are switching threads to follow the schedule
       --Debug.trace ("Switching threads from "++show (tid,step)++" to "++show (tid',step')++"\n") $
       ControlFollow ((tid',step'):sids) tgts     
  | step == step' =
      case (sids,tgts) of
        ([],[]) -> --Debug.trace "Returning to default scheduling\n" $
                   ControlDefault
        ([],_)  -> --Debug.trace "Completed explicit schedule\n" $
                   ControlAwait tgts
        (_,_)   -> --Debug.trace ("Finished step "++show (tid,step)) $
                   ControlFollow sids tgts
  | otherwise =
      error $ "advanceControl "++show (tid,step)++" cannot follow step "++show step'++"\n"
advanceControl stepId (ControlFollow [] tgts)  =
  error $ "advanceControl "++show stepId++" (ControlFollow [] "++show tgts++")"
advanceControl stepId c =
  assert (not $ controlTargets stepId c) $
  c

followControl :: ScheduleControl -> ScheduleControl
followControl (ControlAwait
                 (ScheduleMod{scheduleModTarget,
                              scheduleModInsertion}:
                  mods)) =
  ControlFollow scheduleModInsertion mods

-- Extend an existing schedule control with a newly discovered schedule mod
extendScheduleControl' :: ScheduleControl -> ScheduleMod -> ScheduleControl
extendScheduleControl' ControlDefault m = ControlAwait [m]
extendScheduleControl' (ControlAwait mods) m =
  case scheduleModControl m of
    ControlDefault     -> ControlAwait (mods++[m])
    ControlAwait mods' ->
      let common = length mods - length mods' in
      assert (common >= 0 && drop common mods==mods') $
      ControlAwait (take common mods++[m])
    ControlFollow stepIds mods' ->
      let common = length mods - length mods' - 1
          m'     = mods !! common
          m''    = m'{ scheduleModInsertion =
                         takeWhile (/=scheduleModTarget m)
                                   (scheduleModInsertion m')
                         ++
                         scheduleModInsertion m }
      in
      assert (common >= 0) $
      assert (drop (common+1) mods == mods') $
      assert (scheduleModTarget m `elem` scheduleModInsertion m') $
      ControlAwait (take common mods++[m''])

extendScheduleControl control m =
  let control' = extendScheduleControl' control m in
  {-Debug.trace (unlines ["Extending "++show control,
                        "     with "++show m,
                        "   yields "++show control']) -}
              control'