module LAM.Exec.Test where

import Control.Monad
import LAM.Exec.DBNoTrimPure
import LAM.Exec.DBTrimPure
import LAM.Exec.NamedNoTrimPure
import LAM.IsLAM
import LAM.Parse
import LAM.Print

compareLAMs l l' t = do
  trace1 <- runTrace l  t
  trace2 <- runTrace l' t
  if length trace1 /= length trace2 then return False
    else do comps <- sequence $ zipWith heuristicCompState trace1 trace2
            return $ foldr (&&) True comps
