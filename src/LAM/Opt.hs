module LAM.Opt where

import LAM.Base
import LAM.Parse
import Data.Text (unpack)

-- | Merge let bindings right next to each other if they don't bind
-- any common names.
mergeLet :: Term -> Term
mergeLet (Let x u@(Let y t)) = if or [n == n' | n <- map fst x, n' <- map fst y]
  then (Let x $ mergeLet u)
  else mergeLet (Let (x ++ y) t)
mergeLet (Lam x t) = Lam x (mergeLet t)
mergeLet (App t x) = App (mergeLet t) x
mergeLet (Let x t) = Let (map (\(n,t') -> (n, mergeLet t')) x) (mergeLet t)
mergeLet u = u

-- | If the argument contains subterms of the form @let n = t in (λ
-- n'. t') n@ where @n@ does not appear in @t'@, replace it with @let
-- n' = t[n'/n] in t'@.
inlineLambda :: Term -> Term
inlineLambda (Let u1@[(n, t)] u2@(App (Lam n' t') n'')) =
  if n == n'' && not (isFree t' n)
    then Let [(n', substName t n' n)] (inlineLambda t')
    else Let u1 (inlineLambda u2)
inlineLambda (Lam x t) = Lam x (inlineLambda t)
inlineLambda (App t x) = App (inlineLambda t) x
inlineLambda (Let x t) = Let (map (\(n,t') -> (n, inlineLambda t')) x) (inlineLambda t)
inlineLambda u = u
