module Trie.HashMap where

import Data.HashMap (Map)
import qualified Data.HashMap as Map
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
