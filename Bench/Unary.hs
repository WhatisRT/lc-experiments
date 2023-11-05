module Unary where

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
