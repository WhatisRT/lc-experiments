{-# OPTIONS --sized-types #-}
module Utils.Trie where

open import Data.List hiding (_++_; intersperse; lookup)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_; _<+>_; intersperse; fromList; toList)

import Data.Char.Properties as C
import Data.Trie C.<-strictTotalOrder as T
open import Data.Tree.AVL.Value

open import Utils

private variable A : Set

Trie : Set → Set
Trie A = T.Trie (const _ A) _

instance
  Show-Trie : ∀ {A} → ⦃ Show A ⦄ → Show (Trie A)
  Show-Trie .show t = "{" ++ intersperse "; " (map (λ where (k , v) → fromList k <+> "↦" <+> show v) (T.toList t)) ++ "}"

lookup : Trie A → String → Maybe A
lookup t s = T.lookupValue t (toList s)

delete : Trie A → String → Trie A
delete t s = T.deleteValue (toList s) t

insert : Trie A → String → A → Trie A
insert t s a = T.insert (toList s) a t

insertMulti : Trie A → List (String × A) → Trie A
insertMulti = foldl insert'
  where
    insert' : Trie A → (String × A) → Trie A
    insert' t (s , a) = insert t s a
