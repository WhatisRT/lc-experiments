module Main where

import Control.Monad
import LAM.Exec.DBTrimPure
import LAM.Exec.NamedNoTrimPure
import LAM.IsLAM
import LAM.Parse
import LAM.Pure
import LAM.Base

-- compareLAMs :: (Show s, Show s', PrintableState s, PrintableState s')
--             => IsLAM IO e s t -> IsLAM IO e s' t -> t -> IO Bool
compareLAMs l l' t = do
  trace1' <- runTrace l  t
  trace2' <- runTrace l' t
  -- print (length trace1')
  -- flip mapM_ [0..] (\n -> do
  --                  print =<< (toPrintableState $ trace1' !! n)
  --                  print =<< (toPrintableState $ trace2' !! n))
  trace1 <- traverse toPureState =<< runTrace l  t :: IO [PState NamedList]
  trace2 <- traverse toPureState =<< runTrace l' t :: IO [PState NamedList]
  print $ Prelude.length trace1
  print $ Prelude.length trace2
  forM_ (zip3 [0..] trace1 trace2) (\(i, s1', s2') -> do
    if i `mod` 100 /= 0 then return () else putStrLn ("Step " ++ show i)
    if heuristicCompPState s1' s2' then return ()
      else do putStrLn ("Step " ++ show i ++ ":")
              -- print (trimState s1) >> putStr "\n"
              -- print (trimState s2) >> putStrLn "\n\n"
              -- print s1 >> putStr "\n"
              -- print s2 >> putStr "\n\n"
              -- print s1' >> putStr "\n"
              -- print s2' >> putStr "\n\n"
              -- print s1'' >> putStr "\n"
              -- collectHeap s1'' >>= print >> putStr "\n"
              -- print s2'' >> putStrLn "\n"
              -- collectHeap s2'' >>= print >> putStr "\n\n"
              error "Debug: not equal")

main :: IO ()
main = compareLAMs LAM.Exec.DBTrimPure.isLAMN LAM.Exec.NamedNoTrimPure.isLAM termDebug
  -- printTrace LAMDB.isLAM lamDebug
