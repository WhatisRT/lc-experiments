module LC.Base where

open import Data.List
open import Data.String

Name = String

data Term : Set where
  Var : Name → Term        -- t = x
  Lam : Name → Term → Term -- t = λ x. t'
  App : Term → Term → Term -- t = t' t''

pattern v_ x = Var x
pattern _⟨$⟩_ t t' = App t t'
pattern ƛ_⇒_  x t = Lam x t

AppN : Term → List Term → Term
AppN t []        = t
AppN t (t' ∷ ts) = AppN (App t t') ts
