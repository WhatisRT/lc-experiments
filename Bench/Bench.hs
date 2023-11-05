module Main where

import Criterion.Main

import LAM.IsLAM
import LAM.Parse

import qualified LAM.Exec.NamedNoTrimPure as NamedNoTrimPure
import qualified LAM.Exec.DBNoTrimPure    as DBNoTrimPure
import qualified LAM.Exec.DBNoTrimPure2   as DBNoTrimPure2
import qualified LAM.Exec.DBTrimPure      as DBTrimPure

import Unary
import Scott

runBench l = evalPrint l bench18

benchmarks :: [Benchmark]
benchmarks = [ bench "Unary Nats"              $ whnf benchUNat 18
             , bench "Scott Nats"              $ whnf benchSNat 18
             , bench "NamedNoTrimPure"         $ whnfIO (runBench NamedNoTrimPure.isLAM)
             , bench "DBTrimPure(List)"        $ whnfIO (runBench DBTrimPure.isLAM)
             , bench "DBTrimPure(NamedList)"   $ whnfIO (runBench DBTrimPure.isLAMN)
             , bench "DBNoTrimPure(List)"      $ whnfIO (runBench DBNoTrimPure.isLAM)
             , bench "DBNoTrimPure(NamedList)" $ whnfIO (runBench DBNoTrimPure.isLAMN)
             , bench "DBNoTrimPure(Seq)"       $ whnfIO (runBench DBNoTrimPure.isLAMSeq)
             , bench "DBNoTrimPure(Vec)"       $ whnfIO (runBench DBNoTrimPure.isLAMVec)
             ]

main :: IO ()
main = defaultMain benchmarks
