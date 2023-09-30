module Test where

import Test.QuickCheck

import LAM.Test

doTest t = quickCheck (withMaxSuccess 10000 t)

test :: IO ()
test = do
  doTest roundtripToDB
  doTest roundtripToDBT0
  doTest roundtripToDBT1
