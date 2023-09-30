module LC.Base where

import Data.Text

type Name = Text

data Term
  = Var Name
  | Lam Name Term
  | App Term Term
  deriving Show

appN :: Term -> [Term] -> Term
appN t [] = t
appN t (t':ts) = appN (App t t') ts

mkLet :: Name -> Term -> Term -> Term
mkLet n t t' = App (Lam n t') t
