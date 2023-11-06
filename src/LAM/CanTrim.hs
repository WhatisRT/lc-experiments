-- | Trimming closures.

module LAM.CanTrim (CanTrim(..), collectHeap) where

import LAM.Base

import Data.IORef
import Data.List
import Trie.Map (Trie)
import qualified Data.Map as Map

-- | 'CanTrim' for a term type @term@ and container type @t@ provides
-- a function to trim the enivronment of a closure, i.e. to remove all
-- unused variables. If the term type uses DeBruijn indices, this also
-- has to adjust the indices for the new environment.
class CanTrim term t where
  trim :: Closure term t -> Closure term t

instance CanTrim Term Trie where
  trim (Closure t e) = Closure t $ Map.filterWithKey (\n _ -> n `elem` freeVars t) e

instance CanTrim Term NamedList where
  trim (Closure t (NamedList e)) = Closure t $ NamedList $ filter (\(n, _) -> n `elem` freeVars t) e

instance CanTrim DBTerm NamedList where
  trim (Closure t (NamedList e)) = let free = freeIxs t in
    Closure (mapFree (\i -> maybe undefined id $ findIndex (i ==) free) t) $
      NamedList [e !! x | x <- free]
