module Bench where

import Criterion.Main

import LAM
import LAM.Base
import LAM.Parse

import qualified LAMDB as LAMDB
import qualified LAMDB2 as LAMDB2
import qualified LAMDB3 as LAMDB3

-- import MAlonzo.Code.LAM2

data UNat = UZero | USuc UNat

uAdd :: UNat -> UNat -> UNat
uAdd UZero n = n
uAdd (USuc m) n = USuc (uAdd m n)

uMul :: UNat -> UNat -> UNat
uMul UZero _ = UZero
uMul (USuc m) n = uAdd n (uMul m n)

uSquare :: UNat -> UNat
uSquare n = uMul n n

uLeq :: UNat -> UNat -> Bool
uLeq UZero _ = True
uLeq (USuc m) UZero = False
uLeq (USuc m) (USuc n) = uLeq m n

toUNat 0 = UZero
toUNat n = USuc (toUNat (n - 1))

benchUNat :: Integer -> Bool
benchUNat n = uLeq k k
  where
    k = uSquare (uSquare (toUNat n))

bench1 :: Benchmark
bench1 = bench "Unary Nats" $ whnf benchUNat 18

newtype SNat = MkSNat { runSNat :: forall a. a -> (SNat -> a) -> a }

sZero :: SNat
sZero = MkSNat (\ z s -> z)

sSuc :: SNat -> SNat
sSuc n = MkSNat (\ z s -> s n)

fix :: (a -> a) -> a
fix f = f (fix f)

caseNat :: a -> (SNat -> a) -> SNat -> a
caseNat z s n = runSNat n z s

fixRecNat :: a -> (SNat -> a -> a) -> SNat -> a
fixRecNat z s = fix (\ r -> caseNat z (\ m -> s m (r m)))

sAdd :: SNat -> SNat -> SNat
sAdd n = fixRecNat n (\ k r -> sSuc r)

sMul :: SNat -> SNat -> SNat
sMul n = fixRecNat sZero (\ k r -> sAdd n r)

sSquare :: SNat -> SNat
sSquare n = sMul n n

sLeq :: SNat -> SNat -> Bool
sLeq = fixRecNat (\ _ -> True) (\ d r -> fixRecNat False (\ n d' -> r n))

toSNat 0 = sZero
toSNat n = sSuc (toSNat (n - 1))

benchSNat :: Integer -> Bool
benchSNat n = sLeq k k
  where
    k = sSquare (sSquare (toSNat n))

bench2 :: Benchmark
bench2 = bench "Scott Nats" $ whnf benchSNat 18

--------------------------------------------------------------------------------

lamBench = hsTermBench

benchLAM :: Benchmark
benchLAM = bench "LAM" $ whnfIO (evalPrint isLAM lamBench)

benchDB :: Benchmark
benchDB = bench "LAMDB" $ whnfIO (evalPrint LAMDB.isLAM lamBench)

benchDBN :: Benchmark
benchDBN = bench "LAMDBN" $ whnfIO (evalPrint LAMDB.isLAMN lamBench)

benchDBSeq :: Benchmark
benchDBSeq = bench "LAMDBSeq" $ whnfIO (evalPrint LAMDB.isLAMSeq lamBench)

benchDBVec :: Benchmark
benchDBVec = bench "LAMDBVec" $ whnfIO (evalPrint LAMDB.isLAMVec lamBench)

benchDBT :: Benchmark
benchDBT = bench "LAMDBT" $ whnfIO (evalPrint LAMDB3.isLAM lamBench)

benchDBTN :: Benchmark
benchDBTN = bench "LAMDBTN" $ whnfIO (evalPrint LAMDB3.isLAMN lamBench)

benchmarks :: [Benchmark]
benchmarks = [benchDBT, benchDBTN, Bench.bench1, Bench.bench2, benchLAM, benchDB, benchDBN, benchDBSeq, benchDBVec]

bench' :: IO ()
bench' = defaultMain benchmarks
