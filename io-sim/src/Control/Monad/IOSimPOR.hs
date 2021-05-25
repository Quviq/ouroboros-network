{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Monad.IOSimPOR (
  -- * Simulation monad
  IOSim,
  STMSim,
  -- ** Run simulation
  runSim,
  runSimOrThrow,
  runSimStrictShutdown,
  Failure(..),
  runSimTrace,
  controlSimTrace,
  exploreSimTrace,
  ScheduleControl(..),
  runSimTraceST,
  liftST,
  traceM,
  traceSTM,
  -- * Simulation time
  setCurrentTime,
  unshareClock,
  -- * Simulation trace
  Trace(..),
  TraceEvent(..),
  ThreadLabel,
  Labelled (..),
  traceEvents,
  traceResult,
  selectTraceEvents,
  selectTraceEventsDynamic,
  selectTraceEventsSay,
  printTraceEventsSay,
  selectTraceRaces,
  -- * Eventlog
  EventlogEvent(..),
  EventlogMarker(..),
  -- * Low-level API
  execReadTVar,
  -- * Deprecated interfaces
  SimM,
  SimSTM
  ) where

import           Prelude

import           Data.Dynamic (fromDynamic)
import           Data.List (intercalate)
import           Data.Typeable (Typeable)

import           Control.Exception (throw)

import           Control.Monad.ST.Lazy

import           Control.Monad.Class.MonadThrow as MonadThrow
import           Control.Monad.Class.MonadTime

import           Control.Monad.IOSimPOR.Internal
import           Control.Monad.IOSimPOR.QuickCheckUtils

import           Test.QuickCheck


--import           System.IO
import           System.IO.Unsafe
import           System.Timeout
import           Data.IORef
import qualified Debug.Trace as Debug


selectTraceEvents
    :: (TraceEvent -> Maybe b)
    -> Trace a
    -> [b]
selectTraceEvents fn = go
  where
    go (Trace _ _ _ ev trace) = case fn ev of
      Just x  -> x : go trace
      Nothing ->     go trace
    go (TraceRacesFound _ trace)        = go trace
    go (TraceMainException _ e _)       = throw (FailureException e)
    go (TraceDeadlock      _   threads) = throw (FailureDeadlock threads)
    go (TraceMainReturn    _ _ _)       = []


--selectTraceRaces :: Trace a -> [Control.Monad.IOSimPOR.Internal.ScheduleMod]
selectTraceRaces = go
  where
    go (Trace _ _ _ _ trace)         = go trace
    go (TraceRacesFound races trace) =
      --Debug.trace ("Found "++show (length races) ++" races") $
      races ++ go trace
    go _                             = []

removeTraceRaces :: Trace a -> Trace a
removeTraceRaces = go
  where
    go (Trace a b c d trace)     = Trace a b c d $ go trace
    go (TraceRacesFound _ trace) = go trace
    go t                         = t

-- Extracting races from a trace.  There is a subtlety in doing so: we
-- must return a defined list of races even in the case where the
-- trace is infinite, and there are no races occurring in it! For
-- example, if the system falls into a deterministic infinite loop,
-- then there will be no races to find.

-- In reality we only want to extract races from *the part of the
-- trace used in a test*. We can only observe that by tracking lazy
-- evaluation: only races that were found in the evaluated prefix of
-- an infinite trace should contribute to the "races found". Hence we
-- return a function that returns the races found "so far". This is
-- unsafe, of course, since that function may return different results
-- at different times.

detachTraceRaces trace = unsafePerformIO $ do
  races <- newIORef []
  let readRaces ()  = concat . reverse . unsafePerformIO $ readIORef races
      saveRaces r t = unsafePerformIO $ do
                        modifyIORef races (r:)
                        return t
  let go (Trace a b c d trace)     = Trace a b c d $ go trace
      go (TraceRacesFound r trace) = saveRaces r   $ go trace
      go t                         = t
  return (readRaces,go trace)

-- | Select all the traced values matching the expected type. This relies on
-- the sim's dynamic trace facility.
--
-- For convenience, this throws exceptions for abnormal sim termination.
--
selectTraceEventsDynamic :: forall a b. Typeable b => Trace a -> [b]
selectTraceEventsDynamic = selectTraceEvents fn
  where
    fn :: TraceEvent -> Maybe b
    fn (EventLog dyn) = fromDynamic dyn
    fn _              = Nothing

-- | Get a trace of 'EventSay'.
--
-- For convenience, this throws exceptions for abnormal sim termination.
--
selectTraceEventsSay :: Trace a -> [String]
selectTraceEventsSay = selectTraceEvents fn
  where
    fn :: TraceEvent -> Maybe String
    fn (EventSay s) = Just s
    fn _            = Nothing

-- | Print all 'EventSay' to the console.
--
-- For convenience, this throws exceptions for abnormal sim termination.
--
printTraceEventsSay :: Trace a -> IO ()
printTraceEventsSay = mapM_ print . selectTraceEventsSay

-- | Simulation termination with failure
--
data Failure =
       -- | The main thread terminated with an exception
       FailureException SomeException

       -- | The threads all deadlocked
     | FailureDeadlock ![Labelled ThreadId]

       -- | The main thread terminated normally but other threads were still
       -- alive, and strict shutdown checking was requested.
       -- See 'runSimStrictShutdown'
     | FailureSloppyShutdown [Labelled ThreadId]
  deriving Show

instance Exception Failure where
    displayException (FailureException err) = displayException  err
    displayException (FailureDeadlock threads) =
      concat [ "<<io-sim deadlock: "
             , intercalate ", " (show `map` threads)
             , ">>"
             ]
    displayException (FailureSloppyShutdown threads) =
      concat [ "<<io-sim sloppy shutdown: "
             , intercalate ", " (show `map` threads)
             , ">>"
             ]

-- | 'IOSim' is a pure monad.
--
runSim :: forall a. (forall s. IOSim s a) -> Either Failure a
runSim mainAction = traceResult False (runSimTrace mainAction)

-- | For quick experiments and tests it is often appropriate and convenient to
-- simply throw failures as exceptions.
--
runSimOrThrow :: forall a. (forall s. IOSim s a) -> a
runSimOrThrow mainAction =
    case runSim mainAction of
      Left  e -> throw e
      Right x -> x

-- | Like 'runSim' but also fail if when the main thread terminates, there
-- are other threads still running or blocked. If one is trying to follow
-- a strict thread cleanup policy then this helps testing for that.
--
runSimStrictShutdown :: forall a. (forall s. IOSim s a) -> Either Failure a
runSimStrictShutdown mainAction = traceResult True (runSimTrace mainAction)

traceResult :: Bool -> Trace a -> Either Failure a
traceResult strict = go
  where
    go (Trace _ _ _ _ t)                = go t
    go (TraceRacesFound _ t)            = go t
    go (TraceMainReturn _ _ tids@(_:_))
                               | strict = Left (FailureSloppyShutdown tids)
    go (TraceMainReturn _ x _)          = Right x
    go (TraceMainException _ e _)       = Left (FailureException e)
    go (TraceDeadlock   _   threads)    = Left (FailureDeadlock threads)

traceEvents :: Trace a -> [(Time, ThreadId, Maybe ThreadLabel, TraceEvent)]
traceEvents (Trace time tid tlbl event t) = (time, tid, tlbl, event)
                                          : traceEvents t
traceEvents (TraceRacesFound _ t)         = traceEvents t
traceEvents _                             = []



-- | See 'runSimTraceST' below.
--
runSimTrace :: forall a. (forall s. IOSim s a) -> Trace a
runSimTrace mainAction = removeTraceRaces $ runST (runSimTraceST mainAction)

controlSimTrace :: forall a. ScheduleControl -> (forall s. IOSim s a) -> Trace a
controlSimTrace control mainAction = runST (controlSimTraceST control mainAction)

-- Just an initial version, which tries to reverse ONE race
exploreSimTrace ::
  forall a test. Testable test =>
    Int -> (forall s. IOSim s a) -> (Trace a -> test) -> Property
exploreSimTrace n mainAction k =
  -- ALERT!!! Impure code: readRaces must be called *after* we have
  -- finished with trace.
  let (readRaces,trace) = detachTraceRaces $
                            detectLoopsSimTrace 1000000 $
                              controlSimTrace ControlDefault mainAction
  in k trace .&&.
     let races = take n $ readRaces()
     in tabulate "Number of races explored" [bucket (length races)] $
        conjoinPar
          [ --Debug.trace "New schedule:" $
            --Debug.trace ("  "++show r) $
            counterexample ("Schedule control: " ++ show r) $
            k (removeTraceRaces (detectLoopsSimTrace 1000000 $
                                   controlSimTrace (ControlAwait [r]) mainAction))
          | r <- races ]
  where bucket n | n<10 = show n
        bucket n | n<50 = let n'=show (n `div` 10) in n'++"0-"++n'++"9"
        bucket n        = buck 50
          where buck low | n<2*low = show low++"-"++show (2*low-1)
                         | otherwise = buck (2*low)

-- Detect loops
detectLoopsSimTrace :: Int -> Trace a -> Trace a
detectLoopsSimTrace n trace = go trace
  where go t =
          case unsafePerformIO $ timeout n $ return $! t of
            Nothing                     -> TraceLoop
            Just (Trace a b c d t')     -> Trace a b c d (go t')
            Just (TraceRacesFound a t') -> TraceRacesFound a (go t')
            Just t'                     -> t'

