module LC.Base where

open import Data.List.Membership.Propositional.Properties
open import Data.Bool using (if_then_else_)
open import Data.List
import Data.List.Relation.Unary.Any as Any
open import Data.List.Properties
open import Data.Nat using (ℕ; zero; suc; _≤″_)
open import Data.Nat.Induction
open import Data.Nat.Show
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product
open import Data.String as S hiding (_++_; _≈_; length; _≤_; show)
open import Data.String.Properties
open import Data.List.Membership.DecPropositional (S._≟_)
open import Function
open import Induction.WellFounded
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.On
open import Relation.Binary.Construct.Union
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; cong)
open import Relation.Nullary
open import Relation.Nullary.Decidable

Name = String

data Term : Set where
  Var : Name → Term        -- t = x
  Lam : Name → Term → Term -- t = λ x. t'
  App : Term → Term → Term -- t = t' t''

infixl -1 _⟨$⟩_
infix 0  ƛ_⇒_

pattern v_ x = Var x
pattern _⟨$⟩_ t t' = App t t'
pattern ƛ_⇒_  x t = Lam x t

Let : Name → Term → Term → Term
Let n t t' = (ƛ n ⇒ t') ⟨$⟩ t

AppN : Term → List Term → Term
AppN t []        = t
AppN t (t' ∷ ts) = AppN (App t t') ts

FV : Term → List Name
FV (v x)     = [ x ]
FV (ƛ x ⇒ t) = filter (¬? ∘ (_≟ x)) $ FV t
FV (t ⟨$⟩ t₁) = FV t ++ FV t₁

BV : Term → List Name
BV (v x)     = []
BV (ƛ x ⇒ t) = [ x ]
BV (t ⟨$⟩ t₁) = BV t ++ BV t₁

_[_/_] : Term → Term → Name → Term
(v x₁)     [ t₁ / x ] = if x == x₁ then t₁ else v x₁
(ƛ x₁ ⇒ t) [ t₁ / x ] = if x == x₁ then ƛ x₁ ⇒ t else ƛ x₁ ⇒ t [ t₁ / x ]
(t ⟨$⟩ t₂) [ t₁ / x ] = t [ t₁ / x ] ⟨$⟩ t₂ [ t₁ / x ]

disj : List Name → List Name → Set
disj l l' = ∀ n → n ∈ l → n ∉ l'

-- private variable x y : Name
--                  t t' t₁ : Term

-- infix 0 _≈α_ _∼β>_

-- data Term-cong (R : Term → Term → Set) : Term → Term → Set where
--   base      :           R t  t' → Term-cong R t t'
--   app-cong₁ : Term-cong R t  t' → Term-cong R (App t t₁) (App t' t₁)
--   app-cong₂ : Term-cong R t₁ t' → Term-cong R (App t t₁) (App t t')
--   lam-cong  : Term-cong R t  t' → Term-cong R (Lam x t)  (Lam x t')

-- data _∼α>_ : Term → Term → Set where
--   ren : y ∉ FV t → y ∉ BV t → (ƛ x ⇒ t) ∼α> (ƛ y ⇒ t [ Var y / x ])

-- _≈α_ : Term → Term → Set
-- _≈α_ = EqClosure $ Term-cong _∼α>_



-- len-rec : {A : Set} {B : List A → Set}
--         → ((l : List A) → (((l' : List A) → length l' Data.Nat.< length l → B l') → B l))
--         → (l : List A) → B l
-- len-rec = All.wfRec (wellFounded length <-wellFounded) _ _



-- module GenFree (f : Name → ℕ → Name) (f-inj : ∀ n → Injective _≡_ _≡_ $ f n) where

--   genFree : (ns : List Name) → Name → ∃[ n ] n ∉ ns
--   genFree ns n = case helper ns 0 of λ where (k , pf , _) → genName k , pf
--     where
--       genName : ℕ → Name
--       genName = f n

--       helper : (ns : List Name) → (k : ℕ) → ∃[ k' ] genName k' ∉ ns × k Data.Nat.≤ k'
--       helper = len-rec λ l rec k → let P? = ¬? ∘ (genName k ≟_) in case genName k ∈? l of λ where
--         (yes p) → map₂ (λ where (h₁ , h₂) → (λ h₃ → h₁ $ ∈-filter⁺ P? h₃ $ <⇒≢ h₂ ∘ f-inj n) , <⇒≤ h₂) $
--                     rec (filter P? l) (filter-notAll P? l (Any.map (λ h h' → h' h) p)) (suc k)
--         (no ¬p) → k , ¬p , ≤-refl

--   ∃-disj : ∀ ns t → ∃[ t' ] disj ns (BV t') × (t ≈α t')
--   ∃-disj [] t = t , {!!} , Relation.Binary.Construct.Closure.Equivalence.reflexive (Term-cong _∼α>_)
--   ∃-disj (x ∷ ns) t = {!!}

-- data _∼β>_ : Term → Term → Set where
--   red : disj (FV t₁) (BV t) → App (Lam x t) t₁ ∼β> t [ t₁ / x ]

-- -- data _∼>_ : Term → Term → Set where
-- --   α-conv    : t ≈α  t' →        t ∼> t'
-- --   β-red     : t ∼β> t' →        t ∼> t'
-- --   app-cong₁ : t  ∼> t' → App t t₁ ∼> App t' t₁
-- --   app-cong₂ : t₁ ∼> t' → App t t₁ ∼> App t t'
-- --   lam-cong  : t  ∼> t' → Lam x t  ∼> Lam x t'

-- _≈_ : Term → Term → Set
-- _≈_ = EqClosure $ Term-cong (_≈α_ ∪ _∼β>_)

-- -- data _∶_⇓_∶_ :
