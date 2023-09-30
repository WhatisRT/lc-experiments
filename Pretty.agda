{-# OPTIONS --sized-types #-}
module Pretty where

open import Data.Nat
open import Data.String hiding (show)
open import Function
open import Data.List hiding (_++_; intersperse; replicate; length)
open import Data.Bool
open import Data.Product using (_×_; _,_)

open import Utils

private variable A : Set

record PrettyArgs : Set where
  field indent maxLen pos : ℕ

defArgs : PrettyArgs
defArgs .PrettyArgs.indent = 0
defArgs .PrettyArgs.maxLen = 100
defArgs .PrettyArgs.pos    = 0

record Pretty (A : Set) : Set where
  field pretty' : PrettyArgs → A → String

  pretty : A → String
  pretty = pretty' defArgs

open Pretty ⦃...⦄ public

shouldPrintMulti : PrettyArgs → String → Bool
shouldPrintMulti args s = maxLen <ᵇ length s + pos
  where open PrettyArgs args

newlineIndent : PrettyArgs → String
newlineIndent args = let open PrettyArgs args in "\n" ++ replicate pos ' '

Show⇒Pretty : Show A → Pretty A
Show⇒Pretty s .pretty' _ = show ⦃ s ⦄

instance
  Pretty-ℕ : Pretty ℕ
  Pretty-ℕ = Show⇒Pretty it

  Pretty-String : Pretty String
  Pretty-String .pretty' _ s = s

  Pretty-Product : ∀ {A B} → ⦃ Pretty A ⦄ → ⦃ Pretty B ⦄ → Pretty (A × B)
  Pretty-Product .pretty' args (a , b) = let
    s = pretty' args a ++ "," <+> pretty' args b
    in if shouldPrintMulti args s
      then pretty' args a ++ newlineIndent args ++ "," <+> pretty' args b
      else s

  Pretty-List : ∀ {A} → ⦃ Pretty A ⦄ → Pretty (List A)
  Pretty-List .pretty' args l = let
      open PrettyArgs args
      l' = (map (pretty' args) l)
      len = foldl _⊔_ pos (map Data.String.length l')
      multiline = len <ᵇ maxLen
      sep = if multiline then "; " else newlineIndent args ++ "; "
      init = if multiline then "[ " else "["
    in init ++ intersperse sep l' ++ "]"
