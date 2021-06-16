{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module JohnQC where

import Data.Time.Clock

import Control.Monad
import Control.Monad.IOSimPOR
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadTimer
import Control.Monad.Class.MonadTest

import GHC.Generics

import System.Exit
import System.IO.Unsafe

import Test.QuickCheck
import Data.List
import Control.Exception(try, SomeException)

data Step =
    WhenSet Int Int
  | ThrowTo Int
  | Delay Int
  | Timeout TimeoutStep
  deriving (Eq, Ord, Show)

data TimeoutStep =
    NewTimeout    Int
  | UpdateTimeout Int
  | CancelTimeout
  | AwaitTimeout
  deriving (Eq, Ord, Show, Generic)

instance Arbitrary Step where
  arbitrary = frequency [(5,do m <- choose (1,20)
                               n <- choose (0,m)
                               return $ WhenSet m n),
                         (1,do NonNegative i <- arbitrary
                               return $ ThrowTo i),
                         (1,do Positive i <- arbitrary
                               return $ Delay i),
                         (1,Timeout <$> arbitrary)]

  shrink (WhenSet m n) = map (WhenSet m) (shrink n) ++
                         map (`WhenSet` n) (filter (>=n) (shrink m))
  shrink (ThrowTo i) = map ThrowTo (shrink i)
  shrink (Delay i)   = map Delay (shrink i)
  shrink (Timeout t) = map Timeout (shrink t)

instance Arbitrary TimeoutStep where
  arbitrary = do Positive i <- arbitrary
                 frequency $ map (fmap return) $
                   [(3,NewTimeout i),
                    (1,UpdateTimeout i),
                    (1,CancelTimeout),
                    (3,AwaitTimeout)]

  shrink = genericShrink
  

newtype Task = Task [Step]
  deriving (Eq, Ord, Show)

instance Arbitrary Task where
  arbitrary = do
    steps <- arbitrary
    return . Task $ normalize steps
  shrink (Task steps) =
    (Task <$> compressSteps steps) ++
    (Task . normalize <$> shrink steps)

normalize steps = plug steps wsSteps 1000000
  where wsSteps = reverse $ sort [s | s@(WhenSet _ _) <- steps]
        plug []              []               m = []
        plug (WhenSet _ _:s) (WhenSet a b:ws) m = WhenSet (min a m) (min b m):plug s ws (min b m)
        plug (step:s)        ws               m = step:plug s ws m

compressSteps (WhenSet a b:WhenSet c d:steps) =
  [WhenSet a d:steps] ++ ((WhenSet a b:) <$> compressSteps (WhenSet c d:steps))
compressSteps (s:steps) = (s:) <$> compressSteps steps
compressSteps [] = []

newtype Tasks = Tasks [Task]
  deriving Show

instance Arbitrary Tasks where
  arbitrary = Tasks . fixThrowTos <$> arbitrary
  shrink (Tasks ts) = Tasks . fixThrowTos <$> removeTask ts ++ shrink ts ++ advanceThrowTo ts ++ sortTasks ts

fixThrowTos tasks = mapThrowTos (`mod` length tasks) tasks

removeTask tasks =
  [ mapThrowTos (fixup i) . map (dontThrowTo i) $ take i tasks++drop (i+1) tasks
  | i <- [0..length tasks-1]]
  where fixup i j | j>i       = j-1
                  | otherwise = j
        dontThrowTo i (Task steps) = Task (filter (/=ThrowTo i) steps)

advanceThrowTo [] = []
advanceThrowTo (Task steps:ts) =
  ((:ts) . Task <$> advance steps) ++
  ((Task steps:) <$> advanceThrowTo ts)
  where advance (WhenSet a b:ThrowTo i:steps) =
          [ThrowTo i:WhenSet a b:steps] ++ (([WhenSet a b,ThrowTo i]++) <$> advance steps)
        advance (s:steps) = (s:) <$> advance steps
        advance [] = []

mapThrowTos f tasks = map mapTask tasks
  where mapTask (Task steps) = Task (map mapStep steps)
        mapStep (ThrowTo i) = ThrowTo (f i)
        mapStep s           = s

sortTasks (x:y:xs) | x>y = [y:x:xs] ++ ((x:) <$> sortTasks (y:xs))
sortTasks (x:xs)         = (x:) <$> sortTasks xs
sortTasks []             = []

interpret :: forall s. TVar (IOSim s) Int -> TVar (IOSim s) [ThreadId (IOSim s)] -> Task -> IOSim s (ThreadId (IOSim s))
interpret r t (Task steps) = forkIO $ do
    context <- atomically $ do
      ts <- readTVar t
      when (null ts) retry
      timer <- newTVar Nothing
      return (ts,timer)
    mapM_ (interpretStep context) steps
  where interpretStep _ (WhenSet m n) = atomically $ do
          a <- readTVar r
          when (a/=m) retry
          writeTVar r n
        interpretStep (ts,_) (ThrowTo i) = throwTo (ts !! i) (ExitFailure 0)
        interpretStep _      (Delay i)   = threadDelay (fromIntegral i)
        interpretStep (_,timer) (Timeout tstep) = do
          t <- atomically $ readTVar timer
          case (t,tstep) of
            (_,NewTimeout n)          -> do to <- newTimeout (fromIntegral n)
                                            atomically $ writeTVar timer (Just to)
            (Just to,UpdateTimeout n) -> updateTimeout to (fromIntegral n)
            (Just to,CancelTimeout)   -> cancelTimeout to
            (Just to,AwaitTimeout)    -> atomically $ awaitTimeout to >> return ()
            (Nothing,_)               -> return ()

runTasks :: [Task] -> IOSim s (Int,Int)
runTasks tasks = do
  let m = maximum [maxTaskValue t | Task t <- tasks]
  r  <- atomically $ newTVar m
  t  <- atomically $ newTVar []
  exploreRaces
  ts <- mapM (interpret r t) tasks
  atomically $ writeTVar t ts
  a  <- atomically $ readTVar r
  threadDelay 1000000000  -- allow the SUT threads to run
  return (m,a)

maxTaskValue (WhenSet m _:_) = m
maxTaskValue (_:t)           = maxTaskValue t
maxTaskValue []              = 0

propSimulates :: Tasks -> Property
propSimulates (Tasks tasks) =
  any (not . null . (\(Task steps)->steps)) tasks ==>
    let Right (m,a) = runSim (runTasks tasks) in
    m>=a

propExploration (Tasks tasks) =
  any (not . null . (\(Task steps)->steps)) tasks ==>
    exploreSimTrace 100 (runTasks tasks) $ \trace ->
    counterexample (show trace) $
    case traceResult False trace of
      Right (m,a) -> property $ m>=a
      Left e      -> counterexample (show e) False

testcase = Tasks [Task [ThrowTo 2,WhenSet 0 0],
                  Task [],
                  Task [WhenSet 1 0],
                  Task [ThrowTo 1,
                        ThrowTo 1,
                        WhenSet 1 0,ThrowTo 2,WhenSet 0 0]]


-- Testing propPermutations n should collect every permutation of [1..n] once only.
propPermutations n =
  exploreSimTrace 1000 doit $ \trace ->
    tabulate "Result" [noExceptions $ show $ traceResult False trace] $
      True
  where doit :: IOSim s [Int]
        doit = do
          r <- atomically $ newTVar []
          exploreRaces
          mapM_ (\i -> forkIO $ atomically $ modifyTVar r (++[i])) [1..n]
          atomically $ do
            is <- readTVar r
            when (length is<n) retry
            return is

noExceptions xs = unsafePerformIO $ try (evaluate e) >>= \case
  Right []     -> return []
  Right (x:ys) -> return (x:noExceptions ys)
  Left e       -> return ("\n  "++show (e :: SomeException))