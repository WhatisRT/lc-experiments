module Trie.Map where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text hiding (map)

type Trie = Map Text

empty :: Trie a
empty = Map.empty

insert :: Text -> a -> Trie a -> Trie a
insert = Map.insert

lookup :: Text -> Trie a -> Maybe a
lookup = Map.lookup

insertMulti :: [(Text, a)] -> Trie a -> Trie a
insertMulti l = Map.union (Map.fromList l)

fromList :: [(Text, a)] -> Trie a
fromList = Map.fromList
