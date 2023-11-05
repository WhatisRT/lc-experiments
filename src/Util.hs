module Util where

headMaybe :: [a] -> Maybe a
headMaybe []    = Nothing
headMaybe (a:_) = Just a

lookup :: Int -> [a] -> Maybe a
lookup n l = headMaybe (drop n l)
-- lookup x [] = Nothing
-- lookup x (a : as) = if x == 0 then Just a else Util.lookup (x-1) as

lookupList :: (Eq a) => Int -> [a] -> Maybe a
lookupList _ []       = Nothing
lookupList x (a : as) = if x == 0 then Just a else lookupList (x-1) as

lookup' :: (Eq a, Show a) => Int -> [a] -> a
lookup' i l = case lookupList i l of
  (Just x) -> x
  Nothing  -> error ("lookup': " ++ show i ++ " " ++ show l)
