module Main where

import LAM.Test
import LAM.Pure
import LAM.Parse
import LAM.Exec.Test
import qualified LAM.Exec.DBNoTrimPure as No
import qualified LAM.Exec.DBTrimPure as Yes

import System.Exit
import Test.QuickCheck
import Test.QuickCheck.Monadic


doTest t = isSuccess <$> quickCheckResult (withMaxSuccess 100 t)
doTestSingle t = isSuccess <$> quickCheckResult (withMaxSuccess 1 t)

testBench l = (trueTerm ==) <$> (run $ runHnf l bench18)

tests =
  [ doTest roundtripToDB
  , doTest roundtripToDBT0
  , doTest roundtripToDBT1
  , doTest (\t -> monadicIO $ run (compareLAMs Yes.isLAMN No.isLAMN t))
  , doTestSingle (monadicIO $ testBench No.isLAM)
  , doTestSingle (monadicIO $ testBench No.isLAMN)
  ]

main :: IO ()
main = do
  res <- and <$> sequence tests
  if res then exitSuccess else exitFailure
