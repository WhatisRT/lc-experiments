module LC where

open import LC.Base public
open import LC.Parse
open import Parse

open import Data.Sum
open import Function
open import Data.String
open import Data.Product

parseTerm' : ∀ x → From-inj₁ (runParse parseTerm x)
parseTerm' = from-inj₁ ∘ runParse parseTerm

termId : Term
termId = parseTerm' "λ x. x"

term1 : Term
term1 = parseTerm' "λ x. x x y z"

term2 : Term
term2 = parseTerm' "(λ x. x) y"

term3 : Term
term3 = parseTerm' "(λ x. x x) (λ x. x)"

term2Id : Term
term2Id = parseTerm' "(λ x. x) (λ x. x)"

term5 : Term
term5 = parseTerm' "((λ x. λ y. x x y) (λ x. λ y. x y)) (λ x. x)"

-- term6 : Term
-- term6 = parseTerm' "let zero = λ z. λ s. z; suc = λ n. λ z. λ s. s n in suc (suc zero)"

-- term7 : Term
-- term7 = parseTerm' "let zero = λ z s. z; suc = λ n z s. s n; pred = λ n. n zero (λ k. k) in pred (suc (suc zero))"
