module Utils where

import Data.Char
import Data.String

open import Data.List
open import Data.Bool

private variable A : Set

record EqB (A : Set) : Set where
  field _==_ : A → A → Bool

open EqB ⦃...⦄ public

instance
  EqB-Char : EqB Data.Char.Char
  EqB-Char ._==_ = Data.Char._==_

  EqB-String : EqB Data.String.String
  EqB-String ._==_ = Data.String._==_

_∈ᵇ_ : ⦃ EqB A ⦄ → A → List A → Bool
c ∈ᵇ []       = false
c ∈ᵇ (x ∷ cs) = (c == x) ∨ (c ∈ᵇ cs)
