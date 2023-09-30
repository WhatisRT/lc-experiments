module Containers where

open import Data.Maybe
open import Data.String
open import Data.List using (List)
open import Data.Product

open import Foreign.Haskell
open import Foreign.Haskell.Coerce

{-#
  FOREIGN GHC
  import Data.Map.Strict (Map)
  import qualified Data.Map.Strict as Map

  import Data.Set (Set)
  import qualified Data.Set as Set

  import Data.Text
#-}

-- Maps & sets with strings

private variable
  A : Set

postulate
  Map : Set → Set
  CSet : Set

  lookup : String → Map A → Maybe A
  delete : String → Map A → Map A
  insert : String → A → Map A → Map A
  union  : Map A → Map A → Map A
  restrictKeys : Map A → CSet → Map A
  mapFromList' : List (Pair String A) → Map A
  mapToList' : Map A → List (Pair String A)

  setFromList : List String → CSet

{-# COMPILE GHC Map = type Map Text #-}
{-# COMPILE GHC CSet = type Set Text #-}
{-# COMPILE GHC lookup = \_ -> Map.lookup #-}
{-# COMPILE GHC delete = \_ -> Map.delete #-}
{-# COMPILE GHC insert = \_ -> Map.insert #-}
{-# COMPILE GHC union = \_ -> Map.union #-}
{-# COMPILE GHC restrictKeys = \_ -> Map.restrictKeys #-}
{-# COMPILE GHC mapFromList' = \_ -> Map.fromList #-}
{-# COMPILE GHC mapToList' = \_ -> Map.toList #-}
{-# COMPILE GHC setFromList = Set.fromList #-}

mapFromList : List (String × A) → Map A
mapFromList l = mapFromList' (coerce l)

mapToList : Map A → List (String × A)
mapToList m = coerce (mapToList' m)

insertMulti : List (String × A) → Map A → Map A
insertMulti l = union (mapFromList l)
