module LAM.Exec.NamedNoTrimPure where

import Data.IORef
import LAM.Base
import LAM.IsLAM
import qualified Trie.Map as Trie

mark2 :: State -> IO (Either String State)
mark2 (Closure (Var x) e, s) = case Trie.lookup x e of
  Nothing  -> return (Left "Bug: Var: lookup failed")
  (Just p) -> readIORef p >>= \case
      Nothing -> return (Left "Var: black hole")
      (Just c) -> do
        writeIORef p Nothing -- insert black hole
        return (Right (c, H p : s))
mark2 (Closure (Lam _ _)    e,    [])      = return (Left "Finished: Lam: stack empty")
mark2 (Closure (Lam y e)    env,  P p : s) = return (Right (Closure e (Trie.insert y p env), s))
mark2 (c@(Closure (Lam _ _) env), H p : s) =
  writeIORef p (Just c) >> return (Right (c, s))
mark2 (Closure (App e x)   env, s) = case Trie.lookup x env of
  Nothing  -> return (Left "Bug: App: lookup failed")
  (Just p) -> return (Right (Closure e env, P p : s))
mark2 (Closure t@(Let x e) env, s) = do
  ext <- mapM (\(n, t) -> do r <- newIORef Nothing; return (n, r, t)) x
  let env' = Trie.insertMulti (map (\(n, r, t) -> (n, r)) ext) env
  mapM_ (\(n, r, t) -> writeIORef r (Just (Closure t env'))) ext
  return (Right (Closure e env', s))

isLAM :: IsLAM IO String State Term
isLAM = IsLAM { step = mark2, initS = \t -> (Closure t Trie.empty, []) }

isLAMC :: IsLAM IO String State (Closure Term Trie.Trie)
isLAMC = IsLAM { step = mark2, initS = \t -> (t, []) }
