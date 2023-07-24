{-# OPTIONS --sized-types #-}
module LAM where

open import Utils
import LC
open import LC.Parse

open import Function hiding (const)
open import Data.Nat hiding (_/_)
open import Data.Nat.Show
open import Data.List hiding (lookup)
open import Data.Product hiding (map; zip)
open import Data.String using (String; toList; fromList; _<+>_)
open import Data.Bool
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)

import Data.Char.Properties as C
import Data.Trie C.<-strictTotalOrder as T
open import Data.Tree.AVL.Value

open import Relation.Binary.PropositionalEquality hiding ([_])

private variable A : Set

Name = String

data Term : Set where
  Var : Name → Term                      -- t = x
  Lam : Name → Term → Term               -- t = λ x. t'
  App : Term → Name → Term               -- t = t' x
  Let : List (Name × Term) → Term → Term -- t = let ... in t'

maximum : List ℕ → ℕ
maximum = foldl _⊔_ 0

{-# TERMINATING #-}
freeIndex : Term → ℕ
freeIndex = helper
  where
    toℕ+1 : Name → ℕ
    toℕ+1 n = case runParse parseNat n of λ where
      (inj₁ x) → suc x
      (inj₂ y) → 0

    helper : Term → ℕ
    helper (Var x)   = toℕ+1 x
    helper (Lam x t) = helper t
    helper (App t x) = helper t ⊔ toℕ+1 x
    helper (Let x t) = foldl _⊔_ (helper t) (map (helper ∘ proj₂) x)

free : Term → Name
free = show ∘ freeIndex

AppT : Term → Term → Term
AppT t (Var x) = App t x
AppT t t'      = let x = free t in Let [ (x , t') ] (App t x)

toTerm : LC.Term → Term
toTerm (LC.Var x)    = Var x
toTerm (LC.Lam x t)  = Lam x (toTerm t)
toTerm (LC.App t t₁) = AppT (toTerm t) (toTerm t₁)


{-# TERMINATING #-}
_[_/_] : Term → Term → Name → Term
Var x₁   [ t' / x ] = if x₁ == x then t' else Var x₁
Lam x₁ t [ t' / x ] = if x₁ == x then Lam x₁ t else Lam x₁ (t [ t' / x ])
App t x₁ [ t' / x ] = if x₁ == x then AppT (t [ t' / x ]) t' else App (t [ t' / x ]) x₁
Let l  t [ t' / x ] = if x ∈ᵇ map proj₁ l
  then Let l t
  else Let (map (map₂ _[ t' / x ]) l) (t [ t' / x ])

termId  = toTerm LC.termId
term1   = toTerm LC.term1
term2   = toTerm LC.term2
term2Id = toTerm LC.term2Id
term3   = toTerm LC.term3
term5   = toTerm LC.term5

term4 = Let [ "x" , Var "x" ] (Var "x")

_ : term2Id ≡ term2 [ termId / "y" ]
_ = refl

Trie : Set → Set
Trie A = T.Trie (const _ A) _



HeapPointer Environment Closure Heap Control Stack State Err : Set

HeapPointer = Name

Environment = Trie HeapPointer

Closure = Term × Environment

Heap = Trie Closure

Control = Term

data Tag : Set where
  %_ #_ : HeapPointer → Tag

Stack = List Tag

Err = String

State = Heap × Control × Environment × Stack


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

freeIndexHeap : Heap → ℕ
freeIndexHeap = maximum ∘ map (freeIndex ∘ Var ∘ fromList ∘ proj₁) ∘ T.toList

freeIndexStack : Stack → ℕ
freeIndexStack = maximum ∘ map (freeIndex ∘ Var ∘ λ where (% x) → x ; (# x) → x)

mark2 : State → State ⊎ Err
mark2 (Γ , Var x   , E , S) = case lookup E x of λ where
  nothing  → inj₂ "Bug: Var: lookup failed"
  (just p) → case lookup Γ p of λ where
    nothing          → inj₂ "Var: black hole"
    (just (e' , E')) → inj₁ (delete Γ p , e' , E' , # p ∷ S)
mark2 (Γ , Lam y e     , E , [])        = inj₂ "Finished: Lam: stack empty"
mark2 (Γ , Lam y e     , E , (% p) ∷ S) = inj₁ (Γ , e , insert E y p , S)
mark2 (Γ , t@(Lam _ _) , E , (# p) ∷ S) = inj₁ (insert Γ p (t , E) , t , E , S)
mark2 (Γ , App e x     , E , S) = case lookup E x of λ where
  nothing  → inj₂ "Bug: App: lookup failed"
  (just p) → inj₁ (Γ , e , E , % p ∷ S)
mark2 (Γ , Let x e , E , S) =
  let firstFree = freeIndexHeap Γ ⊔ freeIndexStack S ⊔ freeIndex (Let x e)
      varPairs = zip x $ map (show ∘ (firstFree +_)) $ upTo (length x)
      E' = insertMulti E $ map (λ where ((x , _) , p) → (x , p)) varPairs
  in inj₁ (insertMulti Γ (map (λ where ((_ , e) , p) → p , e , E') varPairs) , e , E' , S)

{-# TERMINATING #-}
mark2' : State → State
mark2' s = case mark2 s of λ where
  (inj₁ s') → mark2' s'
  (inj₂ _)  → s

eval : Term → Term ⊎ Err
eval t = case mark2' (T.empty , t , T.empty , []) of λ where
  (_ , t@(Lam _ _) , _ , []) → inj₁ t
  _                          → inj₂ "Black hole"

{-# TERMINATING #-}
mark2'Trace : State → List State
mark2'Trace s = case mark2 s of λ where
  (inj₁ s') → s ∷ mark2'Trace s'
  (inj₂ _)  → []

evalTrace : Term → List State
evalTrace t = mark2'Trace (T.empty , t , T.empty , [])


-- dom : Heap → List String
-- dom = {!!}



-- [] : let s = λ z. z in let p = (q s); q = (λ y. let r = y in r) in p

-- [s ↦ λ z. z] : let p = (q s); q = (λ y. let r = y in r) in p

--  [s ↦ λ z. z; p ↦ q s; q ↦ λ y. let r = y in r] : p

--   [s ↦ λ z. z; q ↦ λ y. let r = y in r] : q s

--    [s ↦ λ z. z; q ↦ λ y. let r = y in r] : q

--     [s ↦ λ z. z] : λ y. let r = y in r

--    [s ↦ λ z. z; q ↦ λ y. let r = y in r] : hat (λ y. let r = y in r)

--    [s ↦ λ z. z; q ↦ λ y. let r = y in r] : let r = s in r

--     [s ↦ λ z. z; q ↦ λ y. let r = y in r; r ↦ s] : r

--      [s ↦ λ z. z; q ↦ λ y. let r = y in r] : s

--       [q ↦ λ y. let r = y in r] : λ z. z

--      [s ↦ λ z. z; q ↦ λ y. let r = y in r] : hat (λ z. z)

--     [s ↦ λ z. z; q ↦ λ y. let r = y in r; r ↦ hat (λ z. z)] : hat (hat (λ z. z))

--    [s ↦ λ z. z; q ↦ λ y. let r = y in r; r ↦ hat (λ z. z)] : hat (hat (λ z. z))

--   [s ↦ λ z. z; q ↦ λ y. let r = y in r; r ↦ hat (λ z. z)] : hat (hat (λ z. z))

--  [s ↦ λ z. z; q ↦ λ y. let r = y in r; r ↦ hat (λ z. z); p ↦ hat (hat (λ z. z))]
--  : hat (hat (hat (λ z. z)))
