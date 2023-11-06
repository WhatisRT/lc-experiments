-- | Basic lambda calculus definitions.
module LC.Base where

import Data.Text

-- | Variable names.
type Name = Text

-- | Terms.
data Term
  = Var Name
  | Lam Name Term
  | App Term Term
  deriving Show

-- | Apply multiple terms to a single term.
appN :: Term -> [Term] -> Term
appN t [] = t
appN t (t':ts) = appN (App t t') ts

-- | Emulate let-binding
mkLet :: Name -> Term -> Term -> Term
mkLet n t t' = App (Lam n t') t
