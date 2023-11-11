module LAM.Exec.Test where

import LAM.Base
import LAM.IsLAM
import LAM.Pure

compareLAMs :: (ToPureState s1 NamedList, ToPureState s2 NamedList)
  => IsLAM IO e1 s1 t -> IsLAM IO e2 s2 t -> t -> IO Bool
compareLAMs l l' t = do
  trace1 <- traverse toPureState =<< runTraceFinite 1000 l  t :: IO [PState NamedList]
  trace2 <- traverse toPureState =<< runTraceFinite 1000 l' t :: IO [PState NamedList]
  if length trace1 /= length trace2 then return False
    else do comps <- sequence $ zipWith heuristicCompState trace1 trace2
            return $ foldr (&&) True comps
