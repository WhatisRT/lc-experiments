{-# OPTIONS --sized-types #-}
module LAM where

open import Utils
import LC
open import LC.Parse
open import Parse

open import Function hiding (const)
open import Data.Nat hiding (_/_)
open import Data.List hiding (lookup; intersperse) renaming (_++_ to _++L_)
open import Data.Product hiding (map; zip)
open import Data.String using (String; toList; fromList; _<+>_; _++_; intersperse)
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

instance
  {-# TERMINATING #-}
  Show-Term : Show Term
  Show-Term .show (Var x)   = x
  Show-Term .show (Lam x t) = "λ" <+> x Data.String.++ "." <+> show t
  Show-Term .show (App t x) = "(" ++ show t <+> x ++ ")"
  Show-Term .show (Let x t) =
    "let" <+> intersperse "; " (map (λ where (n , t) → n <+> "=" <+> show t) x) <+> "in" <+> show t

termVars : Term → List Name
termVars (Var x) = [ x ]
termVars (Lam x t) = x ∷ termVars t
termVars (App t x) = x ∷ termVars t
termVars (Let x t) = concatMap (λ where (n , t') → n ∷ termVars t) x Data.List.++ termVars t

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
free t = show (freeIndex t)

module Fresh (l : List Name) (n : Name) (k : ℕ) where
  toℕ+1 : Name → ℕ
  toℕ+1 n' = case runParse (exactS n >> parseNat) n' of λ where
    (inj₁ x) → suc x
    (inj₂ y) → 0

  fresh : List Name
  fresh = map (λ p → n ++ show (maximum (map toℕ+1 l) + p)) (upTo k)


{-# TERMINATING #-}
freshName : Name → Term → Name
freshName n t = n ++ show (helper t)
  where
    toℕ+1 : Name → ℕ
    toℕ+1 n' = case runParse (exactS n >> parseNat) n' of λ where
      (inj₁ x) → suc x
      (inj₂ y) → 0

    helper : Term → ℕ
    helper (Var x)   = toℕ+1 x
    helper (Lam x t) = helper t
    helper (App t x) = helper t ⊔ toℕ+1 x
    helper (Let x t) = foldl _⊔_ (helper t) (map (helper ∘ proj₂) x)

freshVar : Name → Term → Term
freshVar n t = Var (freshName n t)

AppT : Term → Term → Term
AppT t (Var x) = App t x
AppT t t'      = let x = freshName "a" t in Let [ (x , t') ] (App t x)

toTerm : LC.Term → Term
toTerm (LC.Var x)    = Var x
toTerm (LC.Lam x t)  = Lam x (toTerm t)
toTerm (LC.App t t₁) = AppT (toTerm t) (toTerm t₁)

fromTerm : Term → LC.Term
fromTerm (Var x)                 = LC.Var x
fromTerm (Lam x t)               = LC.Lam x (fromTerm t)
fromTerm (App t x)               = LC.App (fromTerm t) (LC.Var x)
fromTerm (Let [] t)              = fromTerm t
fromTerm (Let ((x , t') ∷ xs) t) = LC.Let x (fromTerm t') $ fromTerm (Let xs t)

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
term6   = toTerm LC.term6

term4 = Let [ "x" , Var "x" ] (Var "x")

term7 = Let [ "s" , termId ] (Let (("p" , App (Var "q") "s") ∷ [ "q" , Lam "y" (Let [ "r" , Var "y" ] (Var "r")) ]) (Var "p"))
-- let s = λ z. z in let p = (q s); q = (λ y. let r = y in r) in p

bench1   = toTerm LC.bench1


_ : term2Id ≡ term2 [ termId / "y" ]
_ = refl

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

trieVars : Trie A → List Name
trieVars = map (fromList ∘ proj₁) ∘ T.toList

lookupTerm : Trie Term → Name → Term
lookupTerm t n = case lookup t n of λ { (just x) → x ; nothing → Var n }

lookupName : Trie Name → Name → Name
lookupName t n = case lookup t n of λ { (just x) → x ; nothing → n }

substTrie : Trie Term → Term → Term
substTrie t (Var x) = lookupTerm t x
substTrie t (Lam x x₁) = Lam x (substTrie t x₁)
substTrie t (App x x₁) = App {!!} {!!}
substTrie t (Let x x₁) = {!!}


HeapPointer Environment Closure Heap Control Stack State Err : Set

HeapPointer = Name

Environment = Trie HeapPointer

{-# TERMINATING #-}
substEnv : Environment → Term → Term
substEnv t (Var x) = Var (lookupName t x)
substEnv t (Lam x x₁) = Lam x (substEnv t x₁)
substEnv t (App x x₁) = App (substEnv t x) (lookupName t x₁)
substEnv t (Let x x₁) = Let (map (map₂ (substEnv t)) x) (substEnv t x₁)

Closure = Term × Environment

prettyClosure : Closure → String
prettyClosure (t , e) = show (substEnv e t)

Heap = Trie Closure

prettyHeap : Heap → String
prettyHeap = show ⦃ Show-Trie ⦃ λ where .show → prettyClosure ⦄ ⦄

Control = Term

data Tag : Set where
  %_ #_ : HeapPointer → Tag

instance
  Show-Tag : Show Tag
  Show-Tag .show (% x) = "%" <+> x
  Show-Tag .show (# x) = "#" <+> x

Stack = List Tag

Err = String

State = Heap × Control × Environment × Stack

prettyState : State → String
prettyState (Γ , t , E , S) = show (prettyHeap Γ , prettyClosure (t , E) , S)

freeIndexHeap : Heap → ℕ
freeIndexHeap = maximum ∘ map (freeIndex ∘ Var ∘ fromList ∘ proj₁) ∘ T.toList

stackVars : Stack → List Name
stackVars s = map (λ where (% x) → x ; (# x) → x) s

freeIndexStack : Stack → ℕ
freeIndexStack = maximum ∘ map (freeIndex ∘ Var ∘ λ where (% x) → x ; (# x) → x)

mark2Test : State → List String
mark2Test (Γ , Var x   , E , S) = {!!}
mark2Test (Γ , Lam y e     , E , [])        = {!!}
mark2Test (Γ , Lam y e     , E , (% p) ∷ S) = {!!}
mark2Test (Γ , t@(Lam _ _) , E , (# p) ∷ S) = {!!}
mark2Test (Γ , App e x     , E , S) = {!!}
mark2Test (Γ , t@(Let x e) , E , S) =
  trieVars Γ ++L stackVars S ++L termVars t

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
mark2 (Γ , t@(Let x e) , E , S) =
  let varPairs = zip x $ Fresh.fresh (trieVars Γ ++L stackVars S ++L termVars t) "p" (length x)
      E' = insertMulti E $ map (λ where ((x , _) , p) → (x , p)) varPairs
  in inj₁ (insertMulti Γ (map (λ where ((_ , e) , p) → p , e , E') varPairs) , e , E' , S)

{-# TERMINATING #-}
mark2' : State → State
mark2' s = case mark2 s of λ where
  (inj₁ s') → mark2' s'
  (inj₂ _)  → s

initS : Term → State
initS t = (T.empty , t , T.empty , [])

evalN : ℕ → Term → State ⊎ Err
evalN zero t    = inj₁ $ initS t
evalN (suc n) t = case evalN n t of λ where
  (inj₁ x) → mark2 x
  (inj₂ y) → inj₂ ("Error at step" <+> show n ++ ":" <+> y)

eval : Term → Term ⊎ Err
eval t = case mark2' (initS t) of λ where
  (_ , t@(Lam _ _) , _ , []) → inj₁ t
  _                          → inj₂ "Black hole"

{-# TERMINATING #-}
mark2'Trace : State → List State
mark2'Trace s = case mark2 s of λ where
  (inj₁ s') → s ∷ mark2'Trace s'
  (inj₂ _)  → [ s ]

evalTrace : Term → List State
evalTrace t = mark2'Trace (T.empty , t , T.empty , [])




-- {}, let a2 = λ z. λ s. z in (λ zero. let a1 = λ n. λ z. λ s. (s n) in (λ suc. let a0 = (suc zero) in (suc a0) a1) a2), {}, []
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}}, (λ zero. let a1 = λ n. λ z. λ s. (s n) in (λ suc. let a0 = (suc zero) in (suc a0) a1) a2), {a2 ↦ "p0"}, []
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}}, λ zero. let a1 = λ n. λ z. λ s. (s n) in (λ suc. let a0 = (suc zero) in (suc a0) a1), {a2 ↦ "p0"}, [% p0]
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}}, let a1 = λ n. λ z. λ s. (s n) in (λ suc. let a0 = (suc zero) in (suc a0) a1), {a2 ↦ "p0"; zero ↦ "p0"}, []
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}}, (λ suc. let a0 = (suc zero) in (suc a0) a1), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}, []
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}}, λ suc. let a0 = (suc zero) in (suc a0), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}, [% p1]
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}}, let a0 = (suc zero) in (suc a0), {a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}, []
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}; p2 ↦ (suc zero), {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}}, (suc a0), {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}, []
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}; p2 ↦ (suc zero), {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}}, suc, {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}, [% p2]
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p2 ↦ (suc zero), {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}}, λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}, [# p1; % p2]
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}; p2 ↦ (suc zero), {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}}, λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}, [% p2]
-- {p0 ↦ λ z. λ s. z, {a2 ↦ "p0"}; p1 ↦ λ n. λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; zero ↦ "p0"}; p2 ↦ (suc zero), {a0 ↦ "p2"; a1 ↦ "p1"; a2 ↦ "p0"; suc ↦ "p1"; zero ↦ "p0"}}, λ z. λ s. (s n), {a1 ↦ "p1"; a2 ↦ "p0"; n ↦ "p2"; zero ↦ "p0"}, []]"


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
