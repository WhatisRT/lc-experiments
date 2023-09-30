module Utils where

import Data.Char
import Data.Nat.Show

open import Data.Bool
open import Data.List hiding (_++_; intersperse; lookup)
open import Data.Nat
open import Data.String using (String; _++_; _<+>_; intersperse; fromList; toList)
open import Data.Maybe using (Maybe)

private variable A : Set

record EqB (A : Set) : Set where
  field _==_ : A → A → Bool

open EqB ⦃...⦄ public

instance
  EqB-Char : EqB Data.Char.Char
  EqB-Char ._==_ = Data.Char._==_

  EqB-String : EqB Data.String.String
  EqB-String ._==_ = Data.String._==_

  EqB-ℕ : EqB ℕ
  EqB-ℕ ._==_ = _≡ᵇ_

_∈ᵇ_ : ⦃ EqB A ⦄ → A → List A → Bool
c ∈ᵇ []       = false
c ∈ᵇ (x ∷ cs) = (c == x) ∨ (c ∈ᵇ cs)

record Show (A : Set) : Set where
  field show : A → String

open Show ⦃...⦄ public

open import Data.Product hiding (map)
open import Data.Sum hiding (map)


instance
  Show-String : Show String
  Show-String .show s = "\"" ++ s ++ "\""

  Show-ℕ : Show ℕ
  Show-ℕ .show = Data.Nat.Show.show

  Show-List : ∀ {A} → ⦃ Show A ⦄ → Show (List A)
  Show-List .show l = let
      l' = (map show l)
      maxLen = foldl _⊔_ 0 (map Data.String.length l')
      sep = if maxLen <ᵇ 50 then "; " else "\n; "
    in "[" ++ intersperse sep l' ++ "]"

  Show-Product : ∀ {A B} → ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
  Show-Product .show (a , b) = show a ++ "," <+> show b

  Show-Sum : ∀ {A B} → ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A ⊎ B)
  Show-Sum .show (inj₁ x) = "inj₁" <+> show x
  Show-Sum .show (inj₂ y) = "inj₂" <+> show y
