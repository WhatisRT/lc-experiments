module LAM.Exec.DBNoTrimPure where

import LAM.Base hiding (State)
import LAM.Print
import LAM.IsDBEnv
import LAM.IsLAM
import LAM.Types.Generic

import Data.IORef

import Trie.Map (Trie)
import qualified Trie.Map as Trie
import Data.Sequence (Seq)
import Data.Vector (Vector)

type HeapPointer t = RHeapPointer IORef DBTerm t
type Environment t = REnvironment IORef DBTerm t
type Stack t = RStack IORef DBTerm t
type State t = RState IORef DBTerm t

type Err = String

instance PrintableState (State NamedList) where
  toDState = toDStateGen id

mark2 :: IsDBEnv t => State t -> IO (Either Err (State t))
mark2 (Closure (Var x) e, s) = case lookupI x e of
  Nothing  -> return (Left "Bug: Var: lookup failed")
  (Just p) -> do
    r <- readIORef p
    case r of
      Nothing -> return (Left "Var: black hole")
      (Just c) -> do
        writeIORef p Nothing -- insert black hole
        return (Right (c, H p : s))
mark2 (Closure (Lam _ _)   e,   [])      = return (Left "Finished: Lam: stack empty")
mark2 (Closure (Lam y e)   env, P p : s) = return (Right (Closure e (cons y p env), s))
mark2 (Closure t@(Lam _ _) env, H p : s) = let c = Closure t env in do
  writeIORef p (Just c)
  return (Right (c, s))
mark2 (Closure (App e x) env, s) = case lookupI x env of
  Nothing  -> return (Left "Bug: App: lookup failed")
  (Just p) -> return (Right (Closure e env, P p : s))
mark2 (Closure t@(Let x e) env, s) = do
  ext <- mapM (\(n, t) -> do r <- newIORef Nothing; return (n, r, t)) x
  let env' = app (fromList (map (\(n, r, t) -> (n, r)) ext)) env
  mapM_ (\(n, r, t) -> writeIORef r (Just (Closure t env'))) ext
  return (Right (Closure e env', s))


isLAMGC :: IsDBEnv t => IsLAM IO Err (State t) (Term, Trie.Trie (HeapPointer t))
isLAMGC = IsLAM { step = mark2
                , initS = \(t, e) -> (toClosure e t, []) }

isLAMG :: IsDBEnv t => IsLAM IO Err (State t) Term
isLAMG = IsLAM { step = mark2, initS = \t -> (Closure (toDBTerm id t) (fromList []), []) }

isLAM :: IsLAM IO Err (State []) Term
isLAM = isLAMG

isLAMN :: IsLAM IO Err (State NamedList) Term
isLAMN = isLAMG

isLAMSeq :: IsLAM IO Err (State Seq) Term
isLAMSeq = isLAMG

isLAMVec :: IsLAM IO Err (State Vector) Term
isLAMVec = isLAMG
