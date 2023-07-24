module LC.Parse where

open import Data.List
open import Data.String
open import Function
open import LC.Base
open import Parse
open import Utils

parseName : Parse Name
parseName = fromList <$> many+ (noneOf ('(' ∷ ')' ∷ 'λ' ∷ '.' ∷ ' ' ∷ '\n' ∷ []))

{-# TERMINATING #-}
parseTerm parseTerm1 : Parse Term

parseTerm = parseApp ⟨∣⟩ parseTerm1
  where
    parseApp : Parse Term
    parseApp = do
      (t ∷ ts) ← sepBy1 parseTerm1 whitespace+
        where [] → throw "Bug: parseTerm"
      return (AppN t ts)

parseTerm1 = parseVar ⟨∣⟩ parseLam ⟨∣⟩ inParens parseTerm
  where
    parseVar : Parse Term
    parseVar = Var <$> parseName

    parseLam : Parse Term
    parseLam = do
      exact 'λ' >> whitespace+
      n ← parseName
      exact '.' >> whitespace+
      t ← parseTerm
      return (Lam n t)
