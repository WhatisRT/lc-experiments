module LAMDBB where

import LAM.Base hiding (HeapPointer, Environment, Stack, State, Tag, P, H)
import LAM.IsDBEnv

import Data.IORef

import Trie.Map (Trie)
import Data.Sequence (Seq, (<|), (><))
import Data.Vector (Vector)

data Ref t = Box Int | Ref (IORef t)
  deriving Eq

data Tag' a b c = P a | H a | A b c
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Show (Ref t) where
  show = undefined

instance Show (RClosure Ref BVDBTerm t) where
  show = undefined

type HeapPointer t = RHeapPointer Ref BVDBTerm t
type Environment t = REnvironment Ref BVDBTerm t
type Stack t = [Tag' (RHeapPointer Ref BVDBTerm t) BVDBTerm (Environment t)]
type State t = (RClosure Ref BVDBTerm t, Stack t, [Int])

type Err = String

boxed :: IsDBEnv t => Int -> RClosure Ref BVDBTerm t
boxed i = Closure RetDB (fromList [("", Box i)])

unbox :: IsDBEnv t => Environment t -> Int
unbox e = case uncons e of
  Nothing              -> error "Bug: unbox1"
  (Just (_, Box i, _)) -> i
  (Just (_, _, _))     -> error "Bug: unbox2"

mark2 :: IsDBEnv t => State t -> IO (Either Err (State t))
mark2 (Closure (Var x) e, s, s') = case lookupI x e of
  Nothing  -> return (Left "Bug: Var: lookup failed")
  (Just (Box i)) -> return (Left "Bug: Var: looked up box")
  (Just (Ref p)) -> do
    r <- readIORef p
    case r of
      Nothing -> return (Left "Var: black hole")
      (Just c) -> do
        writeIORef p Nothing -- insert black hole
        return (Right (c, H (Ref p) : s, s'))
mark2 (Closure (Lam _ _)   e,   [], _)       = return (Left "Finished: Lam: stack empty")
mark2 (Closure (Lam y e)   env, P p : s, s') = return (Right (Closure e (cons y p env), s, s'))
mark2 (Closure t@(Lam _ _) env, H (Ref p) : s, s') = let c = Closure t env in do
  writeIORef p (Just c)
  return (Right (c, s, s'))
mark2 (Closure (App e x) env, s, s') = case lookupI x env of
  Nothing  -> return (Left "Bug: App: lookup failed")
  (Just p) -> return (Right (Closure e env, P p : s, s'))
mark2 (Closure t@(Let x e) env, s, s') = do
  ext <- mapM (\(n, t) -> do r <- newIORef Nothing; return (n, r, t)) x
  let env' = app (fromList (map (\(n, r, t) -> (n, Ref r)) ext)) env
  mapM_ (\(n, r, t) -> writeIORef r (Just (Closure t env'))) ext
  return (Right (Closure e env', s, s'))
mark2 (Closure (CstDB i) env, s, s') = return (Right (boxed i, s, s'))
mark2 (Closure RetDB n, P p : s, s') = return (Left "Bug: Ret: encounted application")
mark2 (Closure RetDB n, H (Box _) : s, s') = return (Left "Bug: Ret: box")
mark2 (Closure RetDB n, H (Ref p) : s, s') = do
  writeIORef p (Just (boxed (unbox n)))
  return (Right (Closure RetDB n, s, s'))
mark2 (Closure RetDB n, A e env : s, s') = return (Right (Closure e env, s, unbox n : s'))
mark2 (Closure OpPDB env, s, n1 : n2 : s') = return (Right (boxed (n1 + n2), s, s'))
mark2 (Closure OPrDB env, s, n : s') = do
  print n
  return (Right (boxed n, s, s'))
mark2 (Closure (CseDB t t') env, s, s') = return (Right (Closure t env, A t' env : s, s'))
mark2 _ = return (Left "Bug")


isLAMG :: IsDBEnv t => IsLAM IO Err (State t) BVTerm
isLAMG = IsLAM { step = mark2, initS = \t -> (Closure (toDBTerm convBVCtrs t) (fromList []), [], []) }

isLAM :: IsLAM IO Err (State []) BVTerm
isLAM = isLAMG

isLAMN :: IsLAM IO Err (State NamedList) BVTerm
isLAMN = isLAMG

isLAMSeq :: IsLAM IO Err (State Seq) BVTerm
isLAMSeq = isLAMG

isLAMVec :: IsLAM IO Err (State Vector) BVTerm
isLAMVec = isLAMG
