module Util where

import Data.List

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (a:as) = Just a

lookup :: Int -> [a] -> Maybe a
lookup n l = headMaybe (drop n l)
-- lookup x [] = Nothing
-- lookup x (a : as) = if x == 0 then Just a else Util.lookup (x-1) as
