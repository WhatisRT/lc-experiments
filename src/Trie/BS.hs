module Trie.BS where

import qualified Data.Trie as Trie
import Data.Text.Encoding
import Data.Text hiding (map)

type Trie = Trie.Trie

empty :: Trie a
empty = Trie.empty

insert :: Text -> a -> Trie a -> Trie a
insert = Trie.insert . encodeUtf8

lookup :: Text -> Trie a -> Maybe a
lookup = Trie.lookup . encodeUtf8

insertMulti :: [(Text, a)] -> Trie a -> Trie a
insertMulti l = Trie.unionL (Trie.fromList $ map (\(t, v) -> (encodeUtf8 t, v)) l)
