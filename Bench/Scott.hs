module Scott where

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
