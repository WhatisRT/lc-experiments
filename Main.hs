module Main where

import Options.Applicative

import Bench
import Debug
import Test

import LAM.Base
import LAMDB3
import LAMDB

runOnce = evalPrint LAMDB3.isLAM lamBench

data Opts = Opts
  { b :: Bool
  , d :: Bool
  , t :: Bool }

pOpts :: Parser Opts
pOpts = Opts
  <$> switch (long "bench")
  <*> switch (long "debug")
  <*> switch (long "test")

main :: IO ()
main = do -- runOnce
  (Opts b d t) <- execParser $ info pOpts briefDesc
  mif (not b && not t) bench'
  mif d debug
  mif t test
  where
    mif b x = if b then x else return ()
