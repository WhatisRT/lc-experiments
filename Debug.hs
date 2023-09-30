module Debug where

import Control.Monad
import LAM.Parse
import LAM
import LAMDB
import LAMDB3
import LAM.Base
import LAM.Print

lamDebug = hsTermDebug



-- compareLAMs :: (Show s, Show s', PrintableState s, PrintableState s')
--             => IsLAM IO e s t -> IsLAM IO e s' t -> t -> IO Bool
compareLAMs l l' t = do
  trace1' <- runTrace' l  t
  trace2' <- runTrace' l' t
  -- print (length trace1')
  -- flip mapM_ [0..] (\n -> do
  --                  print =<< (toPrintableState $ trace1' !! n)
  --                  print =<< (toPrintableState $ trace2' !! n))
  trace1 <- traverse toDState =<< runTrace' l  t
  trace2 <- traverse toDState =<< runTrace' l' t
  print $ Prelude.length trace1
  print $ Prelude.length trace2
  forM_ (zip3 [0..] trace1 trace2) (\(i, s1', s2') -> do
    let s1 = toPStateD s1'
    let s2 = toPStateD s2'
    let s1'' = trace1' !! i
    let s2'' = trace2' !! i
    if i `mod` 100 /= 0 then return () else putStrLn ("Step " ++ show i)
    if heuristicCompPState s1 s2 then return ()
      else do putStrLn ("Step " ++ show i ++ ":")
              print (trimState s1) >> putStr "\n"
              print (trimState s2) >> putStrLn "\n\n"
              -- print s1 >> putStr "\n"
              -- print s2 >> putStr "\n\n"
              -- print s1' >> putStr "\n"
              -- print s2' >> putStr "\n\n"
              -- print s1'' >> putStr "\n"
              -- collectHeap s1'' >>= print >> putStr "\n"
              -- print s2'' >> putStrLn "\n"
              -- collectHeap s2'' >>= print >> putStr "\n\n"
              error "Debug: not equal")

debug :: IO ()
debug = compareLAMs LAMDB3.isLAMN LAM.isLAM lamDebug
  -- printTrace LAMDB.isLAM lamDebug
