{-# LANGUAGE MagicHash, BangPatterns #-}

-- | Extracting the machine address of a value
module Addr (unsafeAddr) where

import GHC.Exts

data Ptr' a = Ptr' a

aToWord# :: Any -> Word#
aToWord# a = let !mb = Ptr' a in case unsafeCoerce# mb :: Word of W# addr -> addr

-- | Returns the address of any value.
unsafeAddr :: a -> Int
unsafeAddr a = I# (word2Int# (aToWord# (unsafeCoerce# a)))
