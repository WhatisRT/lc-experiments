module Main where

import LAM.Test
import LAM.Exec.Test
import qualified LAM.Exec.DBNoTrimPure as No
import qualified LAM.Exec.DBTrimPure as Yes

import System.Exit
import Test.QuickCheck
import Test.QuickCheck.Monadic


doTest t = isSuccess <$> quickCheckResult (withMaxSuccess 10 t)

main :: IO ()
main = do
  res <- and <$> sequence
    [ doTest roundtripToDB
    , doTest roundtripToDBT0
    , doTest roundtripToDBT1
    , doTest (\ t -> monadicIO $ run (compareLAMs Yes.isLAMN No.isLAMN t) )
    ]
  if res then exitSuccess else exitFailure
