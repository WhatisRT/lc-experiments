module LAMDB where

import Util
import LAM.Base hiding (HeapPointer, Environment, Control, Stack, State)
import LAM.Parse
import LAM.Print

import Data.Text (pack)
import Data.IORef

import Trie.Map (Trie)
import qualified Trie.Map as Trie
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Sequence
import Data.Vector (Vector)
import qualified Data.Vector as Vec


class IsDBEnv t where
  fromList :: [(Name, a)] -> t a
  length :: t a -> Int
  cons :: Name -> a -> t a -> t a
  uncons :: t a -> Maybe (Name, a, t a)
  app  :: t a -> t a -> t a
  lookupI :: Eq a => Int -> t a -> Maybe a
  trimEnv :: [Int] -> t a -> Maybe (t a)
  trimEnv []       _                             = Just $ fromList []
  trimEnv (0:is)   e | Just (n,v,vs) <- uncons e = cons n v <$> trimEnv (map (\x -> x-1) is) vs
  trimEnv is@(_:_) e | Just (_,_,vs) <- uncons e = trimEnv (map (\x -> x-1) is) vs
  trimEnv _        _                             = Nothing

instance IsDBEnv [] where
  fromList = map snd
  length = Prelude.length
  cons _ = (:)
  uncons (x:xs) = Just (pack "",x,xs)
  uncons [] = Nothing
  app = (++)
  lookupI = Util.lookup


instance IsDBEnv NamedList where
  fromList = NamedList
  length (NamedList l) = Prelude.length l
  cons n t (NamedList l) = NamedList ((n, t) : l)
  uncons (NamedList ((n,x):xs)) = Just (n,x,NamedList xs)
  uncons (NamedList []) = Nothing
  app (NamedList l) (NamedList l') = NamedList (l ++ l')
  lookupI i (NamedList l) = Util.lookup i (map snd l)

instance IsDBEnv Seq where
  fromList = Sequence.fromList . map snd
  cons _ = (<|)
  app = (><)
  lookupI = Sequence.lookup

instance IsDBEnv Vector where
  fromList = Vec.fromList . map snd
  cons _ = Vec.cons
  app = (Vec.++)
  lookupI = flip (Vec.!?)

type HeapPointer t = RHeapPointer IORef DBTerm t
type Environment t = REnvironment IORef DBTerm t
type Stack t = RStack IORef DBTerm t
type State t = RState IORef DBTerm t

type Err = String

convHeap :: RHeap DBTerm NamedList -> DHeap
convHeap h = map (\(Ref a, c) -> (Ref a, fmap convClosure' c)) h

convClosure' :: RClosure Ref DBTerm NamedList -> RClosure Ref Term Trie
convClosure' (Closure t (NamedList e)) =
  Closure (fromDBTermCtx (map fst e) t) (Trie.fromList $ reverse $ map (\(n, r) -> (n, convRef r)) e)

convState' :: RState Ref DBTerm NamedList -> RState Ref Term Trie
convState' (c, s) = (convClosure' c, map (fmap convRef) s)

instance PrintableState (State NamedList) where
  toDState state = do
    h <- collectHeap state
    h' <- convHeap' h
    s' <- convStateRef (ioToRefH h) state
    return (convHeap h', convState' s')

mark2 :: IsDBEnv t => State t -> IO (Either Err (State t))
mark2 (Closure (DBVar x) e, s) = case lookupI x e of
  Nothing  -> return (Left "Bug: Var: lookup failed")
  (Just p) -> do
    r <- readIORef p
    case r of
      Nothing -> return (Left "Var: black hole")
      (Just c) -> do
        writeIORef p Nothing -- insert black hole
        return (Right (c, H p : s))
mark2 (Closure (DBLam _ _)   e,   [])      = return (Left "Finished: Lam: stack empty")
mark2 (Closure (DBLam y e)   env, P p : s) = return (Right (Closure e (cons y p env), s))
mark2 (Closure t@(DBLam _ _) env, H p : s) = let c = Closure t env in do
  writeIORef p (Just c)
  return (Right (c, s))
mark2 (Closure (DBApp e x) env, s) = case lookupI x env of
  Nothing  -> return (Left "Bug: App: lookup failed")
  (Just p) -> return (Right (Closure e env, P p : s))
mark2 (Closure t@(DBLet x e) env, s) = do
  ext <- mapM (\(n, t) -> do r <- newIORef Nothing; return (n, r, t)) x
  let env' = app (fromList (map (\(n, r, t) -> (n, r)) ext)) env
  mapM_ (\(n, r, t) -> writeIORef r (Just (Closure t env'))) ext
  return (Right (Closure e env', s))


isLAMG :: IsDBEnv t => IsLAM IO Err (State t) Term
isLAMG = IsLAM { step = mark2, initS = \t -> (Closure (toDBTerm t) (fromList []), []) }

isLAM :: IsLAM IO Err (State []) Term
isLAM = isLAMG

isLAMN :: IsLAM IO Err (State NamedList) Term
isLAMN = isLAMG

isLAMSeq :: IsLAM IO Err (State Seq) Term
isLAMSeq = isLAMG

isLAMVec :: IsLAM IO Err (State Vector) Term
isLAMVec = isLAMG
