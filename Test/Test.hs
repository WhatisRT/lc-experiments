module Main where

import LAM.Test

import Test.QuickCheck

doTest t = quickCheck (withMaxSuccess 10000 t)

main :: IO ()
main = do
  doTest roundtripToDB
  doTest roundtripToDBT0
  doTest roundtripToDBT1
