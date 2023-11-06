-- | Helper functions.
module Util (lookupList) where

-- |
lookupList :: Int -> [a] -> Maybe a
lookupList _ []       = Nothing
lookupList x (a : as) = if x == 0 then Just a else lookupList (x-1) as
