module LAM.Base where

import LC
open import Parse using (runParse; parseNat; exactS)
open import Utils

open import Data.Bool
open import Data.List hiding (lookup; intersperse) renaming (_++_ to _++L_)
open import Data.Nat
open import Data.Product hiding (map; zip)
open import Data.String using (String; toList; fromList; _<+>_; _++_; intersperse)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function

open import Foreign.Haskell
open import Foreign.Haskell.Coerce

private variable A B : Set

{-# FOREIGN GHC
  import Data.Text
  import Text.Pretty.Simple
  import Text.Pretty.Simple.Internal.Color

  opts = defaultOutputOptionsDarkBg
    { outputOptionsIndentAmount  = 1
    , outputOptionsCompact       = True
    , outputOptionsCompactParens = False
    , outputOptionsPageWidth     = 240
    , outputOptionsColorOptions  = Just (defaultColorOptionsDarkBg { colorString = colorBold Vivid Yellow })}

  type Name = Text

  data Term
    = Var Name
    | Lam Name Term
    | App Term Name
    | Let [(Name, Term)] Term

  instance Show Term where
    show = unpack . showTerm

  data Tag a = P a
             | H a deriving Show

  type HeapPointer = Integer
  type Heap = [(HeapPointer, Maybe Closure)]
  type Closure = (Term, Environment)
  type Stack = [Tag HeapPointer]
  type Environment = [(Text, HeapPointer)]

  data State = State { heap :: Heap, closure :: Closure, stack :: Stack } deriving Show
#-}

Name = String

module Foreign where

  data Term : Set where
    Var : Name → Term
    Lam : Name → Term → Term
    App : Term → Name → Term
    Let : List (Pair Name Term) → Term → Term

  {-# COMPILE GHC Term = data Term (Var | Lam | App | Let) #-}

data Term : Set where
  Var : Name → Term                      -- t = x
  Lam : Name → Term → Term               -- t = λ x. t'
  App : Term → Name → Term               -- t = t' x
  Let : List (Name × Term) → Term → Term -- t = let ... in t'

instance
  Coercible-Term : Coercible Term Foreign.Term
  Coercible-Term = TrustMe

  Coercible-Term' : Coercible Foreign.Term Term
  Coercible-Term' = TrustMe

  {-# TERMINATING #-}
  Show-Term : Show Term
  Show-Term .show (Var x)   = x
  Show-Term .show (Lam x t) = "λ" <+> x Data.String.++ "." <+> show t
  Show-Term .show (App t x) = "(" ++ show t <+> x ++ ")"
  Show-Term .show (Let x t) =
    "let" <+> intersperse "; " (map (λ where (n , t) → n <+> "=" <+> show t) x) <+> "in" <+> show t

showTerm : Foreign.Term → String
showTerm = show ∘ coerce

{-# COMPILE GHC showTerm as showTerm #-}

termVars : Term → List Name
termVars (Var x) = [ x ]
termVars (Lam x t) = x ∷ termVars t
termVars (App t x) = x ∷ termVars t
termVars (Let x t) = concatMap (λ where (n , t') → n ∷ termVars t) x ++L termVars t

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

-- module Fresh (l : List Name) (n : Name) (k : ℕ) where
--   toℕ+1 : Name → ℕ
--   toℕ+1 n' = case runParse (exactS n >> parseNat) n' of λ where
--     (inj₁ x) → suc x
--     (inj₂ y) → 0

--   fresh : List Name
--   fresh = map (λ p → n ++ show (maximum (map toℕ+1 l) + p)) (upTo k)


{-# TERMINATING #-}
freshName : String → Term → Name
freshName n t = n ++ show (helper t)
  where
    toℕ+1 : Name → ℕ
    toℕ+1 n' = case runParse (exactS n Parse.>> parseNat) n' of λ where
      (inj₁ x) → suc x
      (inj₂ y) → 0

    helper : Term → ℕ
    helper (Var x)   = toℕ+1 x
    helper (Lam x t) = helper t
    helper (App t x) = helper t ⊔ toℕ+1 x
    helper (Let x t) = foldl _⊔_ (helper t) (map (helper ∘ proj₂) x)

freshVar : String → Term → Term
freshVar n t = Var (freshName n t)

{-# TERMINATING #-}
freeVars : Term → List Name
freeVars = helper []
  where
    helper : List Name → Term → List Name
    helper B (Var x) = if x ∈ᵇ B then [] else [ x ]
    helper B (Lam x t) = helper (x ∷ B) t
    helper B (App t x) = helper B t ++L helper B (Var x)
    helper B (Let x t) = let B' = map proj₁ x ++L B in
      concatMap (helper B' ∘ proj₂) x ++L helper B' t

freeVarsU : Term → List Name
freeVarsU = deduplicate Data.String._≟_ ∘ freeVars

AppT : Term → Term → Term
AppT t (Var x) = App t x
AppT t t'      = let x = freshName "a" t in Let [ (x , t') ] (App t x)

toTerm : LC.Term → Term
toTerm (LC.Var x)    = Var x
toTerm (LC.Lam x t)  = Lam x (toTerm t)
toTerm (LC.App t t₁) = AppT (toTerm t) (toTerm t₁)

withFix : Term → Term
withFix t = Let [ "fix" , Lam "f" (Let [ "fixf" , App (Var "fix") "f" ] (App (Var "f") "fixf")) ] t
