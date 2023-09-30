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

term6 : Term
term6 = parseTerm' "let zero = λ z. λ s. z in let suc = λ n. λ z. λ s. s n in suc (suc zero)"

defs' : String
defs' =  "let zero = λ z. λ s. z
      in let suc = λ n. λ z. λ s. s n
      in let caseNat = λ z. λ s. λ n. n z s
      in let fixRecNat = λ z. λ s. fix (λ rec. caseNat z (λ m. s m (rec m)))
      in let add = λ n. fixRecNat n (λ k. λ rec. suc rec)
      in let one = suc zero
      in let two = suc one
      in "

defs : String
defs =  "let zero = λ z. λ s. z
      in let suc = λ n. λ z. λ s. s n
      in let caseNat = λ z. λ s. λ n. n z s
      in let fixRecNat = λ z. λ s. fix (λ rec. caseNat z (λ m. s m (rec m)))
      in let add = λ n. fixRecNat n (λ k. λ rec. suc rec)
      in let mul = λ n. fixRecNat zero (λ k. λ rec. add n rec)
      in let square = λ n. mul n n
      in let true = λ f. λ t. t
      in let false = λ f. λ t. f
      in let leq = fixRecNat (λ d. true) (λ d. λ rec. fixRecNat false (λ n. λ d'. rec n))
      in let one = suc zero
      in let two = suc one
      in let three = suc two
      in let four = square two
      in let eight = square two
      in let nine = suc eight
      in let ten = suc nine
      in let sixteen = square four
      in "

test1 : Term
test1 = parseTerm' (defs' ++ "add two two")

bench1 : Term
bench1 = parseTerm' (defs ++ "leq (square two) (square two)")

bench2 : Term
bench2 = parseTerm' (defs ++ "leq (square (square four)) (square (square four))")

bench3 : Term
bench3 = parseTerm' (defs ++ "let v = square (square (add ten three)) in leq v v")

bench4 : Term
bench4 = parseTerm' (defs ++ "let v = square (square (add ten eight)) in leq v v")



-- term7 : Term
-- term7 = parseTerm' "let zero = λ z s. z; suc = λ n z s. s n; pred = λ n. n zero (λ k. k) in pred (suc (suc zero))"
