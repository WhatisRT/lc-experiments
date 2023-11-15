module Main where

import LAM.Test
import LAM.Pure
import LAM.Parse
import LAM.Exec.Test
import LAM.Base
--import qualified LAM.Exec.DBNoTrimEff as NoTrimEff
import qualified LAM.Exec.DBNoTrimPure as NoTrimPure
import qualified LAM.Exec.DBTrimPure as TrimPure

import System.Exit
import Test.QuickCheck
import Test.QuickCheck.Monadic


doTest t = isSuccess <$> quickCheckResult (withMaxSuccess 100 t)
doTestSingle t = isSuccess <$> quickCheckResult (withMaxSuccess 1 t)

testBench l = (trueTerm ==) <$> (run $ runHnf l bench18)


list_of_LAMs :: [LAM Term]
list_of_LAMs = [
                 Any NoTrimPure.isLAM
              -- , Any NoTrimPure.isLAMN
               , Any NoTrimPure.isLAMSeq
               , Any NoTrimPure.isLAMVec
              -- , Any TrimPure.isLAMN
               ]

tests_LAM = let n = length list_of_LAMs
            in [ doTest (\t -> monadicIO $ run (compareLAMs' (list_of_LAMs!!i) (list_of_LAMs!!j) t))
            | i <- [0..(n-1)] , j <- [(i+1)..(n-1)] ]

tests =
  [ doTest roundtripToDB
  , doTest roundtripToDBT0
  , doTest roundtripToDBT1
  , doTest (\t -> monadicIO $ run (compareLAMs TrimPure.isLAMN NoTrimPure.isLAMN t))
  , doTestSingle (monadicIO $ testBench NoTrimPure.isLAM)
  , doTestSingle (monadicIO $ testBench NoTrimPure.isLAMN)
  ]

main :: IO ()
main = do
  res <- and <$> sequence (tests ++ tests_LAM)
  if res then exitSuccess else exitFailure
