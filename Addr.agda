module Addr where

{-# FOREIGN GHC   {-# LANGUAGE MagicHash, BangPatterns #-} #-}

open import Data.Nat

{-#
  FOREIGN GHC
  import GHC.Exts

  -- A datatype that has the same layout as Word and so can be casted to it.
  data Ptr' a = Ptr' a

  -- Any is a type to which any type can be safely unsafeCoerced to.
  aToWord# :: Any -> Word#
  aToWord# a = let !mb = Ptr' a in case unsafeCoerce# mb :: Word of W# addr -> addr

  unsafeAddr :: a -> Int
  unsafeAddr a = I# (word2Int# (aToWord# (unsafeCoerce# a)))
#-}

postulate unsafeAddr : {A : Set} → A → ℕ

{-# COMPILE GHC unsafeAddr = \ _ -> fromIntegral . unsafeAddr #-}
