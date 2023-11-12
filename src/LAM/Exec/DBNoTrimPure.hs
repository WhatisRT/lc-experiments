module LAM.Exec.DBNoTrimPure where

import LAM.Base hiding (State)
import LAM.CanTrim
import LAM.Pure
import LAM.IsDBEnv
import LAM.IsLAM
import Trie.Map (Trie)

import Data.Foldable
import Data.IORef

import qualified Trie.Map as Trie
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Vector (Vector)
import qualified Data.Vector as Vec

type HeapPointer t = RHeapPointer IORef DBTerm t
type State t = RState IORef DBTerm t

type Err = String

instance IsNamedEnv Seq where
  eToList s = eToList $ toList s
  eFromList l = Seq.fromList $ eFromList l

instance IsNamedEnv Vector where
  eToList s = eToList $ toList s
  eFromList l = Vec.fromList $ eFromList l

instance CanTrim DBTerm [] where
  trim c = c

instance CanTrim DBTerm Seq where
  trim c = c

instance CanTrim DBTerm Vector where
  trim c = c

instance ToPureState (State NamedList) NamedList where
  toPureState = toPureStateGen id

instance ToPureState (State NamedList) Trie where
  toPureState = toPureStateGen id

instance ToPureState (State []) Trie where
  toPureState = toPureStateGen id

instance ToPureState (State Seq) Trie where
  toPureState = toPureStateGen id

instance ToPureState (State Vector) Trie where
  toPureState = toPureStateGen id

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
