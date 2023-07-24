module Parse where

open import Data.Bool
open import Data.Char as C
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Data.Product
open import Data.String as S
open import Data.Sum
open import Data.Unit
open import Function
open import Utils

private variable A B : Set

ParseErr = String

Parse : Set → Set
Parse A = String → (A × String) ⊎ ParseErr

Err : Set → Set
Err A = A ⊎ String

runParse : Parse A → String → A ⊎ ParseErr
runParse p s = case p s of λ where
  (inj₁ (a , "")) → inj₁ a
  (inj₁ (a , s))  → inj₂ "Not all input was consumed"
  (inj₂ e)        → inj₂ e

runParse' : Parse A → String → (A × String) ⊎ ParseErr
runParse' p s = p s

return : A → Parse A
return a = λ s → inj₁ (a , s)

infixl 1 _>>_ _>>=_ _⟨∣⟩_

_>>=_ : Parse A → (A → Parse B) → Parse B
x >>= f = λ s → case x s of λ where
  (inj₁ (a , s')) → f a s'
  (inj₂ y)        → inj₂ y

_<$>_ : (A → B) → Parse A → Parse B
f <$> x = x >>= (return ∘ f)

_>>_ : Parse A → Parse B → Parse B
x >> y = x >>= (λ _ → y)

void : Parse A → Parse ⊤
void p = p >> return _

throw : ParseErr → Parse A
throw e = λ _ → inj₂ e

catch : Parse A → (ParseErr → Parse A) → Parse A
catch p f = λ s → case p s of λ where
  (inj₁ x) → inj₁ x
  (inj₂ y) → f y s

_⟨∣⟩_ : Parse A → Parse A → Parse A
p₁ ⟨∣⟩ p₂ = catch p₁ (λ _ → p₂)

-- parse a single character satisfying a predicate
parseIfTrue : (Char → Bool) → Parse Char
parseIfTrue f s = case S.uncons s of λ where
  (just (c , s')) → if f c
                      then inj₁ (c , s')
                      else inj₂ ("Tried to parse a disallowed character:" <+> S.fromList [ c ])
  nothing         → inj₂ "Tried to parse a character while the string was empty"


-- parse a single character in the list
oneOf : List Char → Parse Char
oneOf cs = parseIfTrue (_∈ᵇ cs)

-- parse a single character not in the list
noneOf : List Char → Parse Char
noneOf cs = parseIfTrue (not ∘ _∈ᵇ cs)

-- parse a single given character
exact : Char → Parse Char
exact c = oneOf [ c ]

{-# TERMINATING #-}
many : Parse A → Parse (List A)
many p = (p >>= λ a → (a ∷_) <$> many p) ⟨∣⟩ return []

-- parse a non-empty list
many+ : Parse A → Parse (List A)
many+ p = p >>= λ a → (a ∷_) <$> many p

whitespace1 : Parse ⊤
whitespace1 = void $ oneOf (' ' ∷ '\n' ∷ [])

whitespace+ : Parse ⊤
whitespace+ = void $ many+ whitespace1

sepBy1 : Parse A → Parse B → Parse (List A)
sepBy1 p sep = p >>= λ a → (a ∷_) <$> many (sep >> p)

inParens : Parse A → Parse A
inParens p = do
  exact '('
  res ← p
  exact ')'
  return res

parseDigit : Parse ℕ
parseDigit = ((_∸ 48) ∘ toℕ) <$> oneOf ('0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷ [])

parseNat : Parse ℕ
parseNat = foldl (λ acc k → 10 * acc + k) 0 <$> many+ parseDigit
