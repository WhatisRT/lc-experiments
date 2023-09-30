module Trie.IntMap where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Text hiding (IntMap)

type Trie = IntMap

empty :: Trie a
empty = IntMap.empty

insert :: Int -> a -> Trie a -> Trie a
insert = IntMap.insert

lookup :: Int -> Trie a -> Maybe a
lookup = IntMap.lookup

insertMulti :: [(Int, a)] -> Trie a -> Trie a
insertMulti l = IntMap.union (IntMap.fromList l)
