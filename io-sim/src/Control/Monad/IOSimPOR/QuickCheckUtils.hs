module Control.Monad.IOSimPOR.QuickCheckUtils where

import Test.QuickCheck.Property
import Control.Parallel

-- Take the conjunction of several properties, in parallel
-- This is a clone of code from Test.QuickCheck.Property,
-- modified to run non-IO properties in parallel.
conjoinPar :: Testable prop => [prop] -> Property
conjoinPar ps =
  again $
  MkProperty $
  do roses <- mapM (fmap unProp . unProperty . property) ps
     return (MkProp (conj id (speculate roses)))
 where
  -- speculation tries to evaluate each Rose tree in parallel, to WHNF
  -- This will not perform any IO, but should evaluate non-IO properties
  -- completely.
  speculate [] = []
  speculate (rose:roses) = rose `par` speculate roses `par` (rose:roses)

  conj k [] =
    MkRose (k succeeded) []

  conj k (p : ps) = IORose $ do
    rose@(MkRose result _) <- reduceRose p
    case ok result of
      _ | not (expect result) ->
        return (return failed { reason = "expectFailure may not occur inside a conjunction" })
      Just True -> return (conj (addLabels result . addCallbacksAndCoverage result . k) ps)
      Just False -> return rose
      Nothing -> do
        rose2@(MkRose result2 _) <- reduceRose (conj (addCallbacksAndCoverage result . k) ps)
        return $
          -- Nasty work to make sure we use the right callbacks
          case ok result2 of
            Just True -> MkRose (result2 { ok = Nothing }) []
            Just False -> rose2
            Nothing -> rose2

  addCallbacksAndCoverage result r =
    r { callbacks = callbacks result ++ callbacks r,
        requiredCoverage = requiredCoverage result ++ requiredCoverage r }
  addLabels result r =
    r { labels = labels result ++ labels r,
        classes = classes result ++ classes r,
        tables = tables result ++ tables r }