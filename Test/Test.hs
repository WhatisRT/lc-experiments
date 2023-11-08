module Main where

import LAM.Test

import System.Exit
import Test.QuickCheck

doTest t = isSuccess <$> quickCheckResult (withMaxSuccess 10000 t)

main :: IO ()
main = do
  res <- and <$> sequence
    [ doTest roundtripToDB
    , doTest roundtripToDBT0
    , doTest roundtripToDBT1
    ]
  if res then exitSuccess else exitFailure
