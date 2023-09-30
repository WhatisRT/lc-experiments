module LC.Parse where

open import Data.Bool
open import Data.List
open import Data.String hiding (_==_)
open import Function
open import LC.Base
open import Parse
open import Utils

keywords : List Name
keywords = "let" ∷ "in" ∷ []

parseName : Parse Name
parseName = do
  n ← fromList <$> many+ (noneOf ('(' ∷ ')' ∷ 'λ' ∷ '.' ∷ ';' ∷ '=' ∷ ' ' ∷ '\n' ∷ []))
  if n ∈ᵇ keywords then throw (n <+> "can not be a name since it is a keyword!") else return n

{-# TERMINATING #-}
parseTerm parseTerm1 : Parse Term

parseTerm = parseApp ⟨∣⟩ parseTerm1
  where
    parseApp : Parse Term
    parseApp = do
      (t ∷ ts) ← sepBy1 parseTerm1 whitespace+
        where [] → throw "Bug: parseTerm"
      return (AppN t ts)

parseTerm1 = parseLet ⟨∣⟩ parseVar ⟨∣⟩ parseLam ⟨∣⟩ inParens parseTerm
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

    parseLet : Parse Term
    parseLet = do
      exactS "let" >> whitespace+
      n ← parseName
      whitespace+ >> exact '=' >> whitespace+
      t ← parseTerm
      whitespace+ >> exactS "in" >> whitespace+
      t' ← parseTerm
      return (Let n t t')
