module John where

import Control.Monad
import Control.Monad.IOSimPOR
import Control.Monad.Class.MonadSTM
import Control.Monad.Class.MonadFork

doit :: IOSim s Integer
doit = do
  r <- atomically $ newTVar 0
  forkIO $ atomically $ modifyTVar r (+1)
  forkIO $ atomically $ modifyTVar r (+1)
  atomically $ do
    a <- readTVar r
    when (a==0) retry
    return a
    --retry

