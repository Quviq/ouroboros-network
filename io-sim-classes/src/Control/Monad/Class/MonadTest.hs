
module Control.Monad.Class.MonadTest where

class Monad m => MonadTest m where
  exploreRaces :: m ()

