module LAM.Exec.DBTrimPure where

import Data.IORef
import LAM.Base hiding (HeapPointer, Environment, Stack, State)
import LAM.IsDBEnv
import LAM.IsLAM
import LAM.Print hiding (convHeap'')
import LAM.Trim
--import LAMDB hiding (HeapPointer, Environment, Stack, State, mark2)
import Trie.Map (Trie)
import qualified Trie.Map as Trie

type HeapPointer t = RHeapPointer IORef DBTTerm0 t
type Environment t = REnvironment IORef DBTTerm0 t
type Stack t = RStack IORef DBTTerm0 t
type State t = RState IORef DBTTerm0 t

type Err = String

convHeap'' :: RHeap DBTTerm0 NamedList -> DHeap
convHeap'' h = map (\(Ref a, c) -> (Ref a, fmap convClosure'' c)) h

convClosure'' :: RClosure Ref DBTTerm0 NamedList -> RClosure Ref Term Trie
convClosure'' (Closure t (NamedList e)) =
  Closure (fromDBTermCtx id (map fst e) $ fromDBTTerm0 t)
          (Trie.fromList $ reverse $ map (\(n, r) -> (n, convRef r)) e)

convState'' :: RState Ref DBTTerm0 NamedList -> RState Ref Term Trie
convState'' (c, s) = (convClosure'' c, map (fmap convRef) s)

instance Show (Closure DBTTerm0 t) where
  show (Closure t _) = show t

instance CanTrim DBTTerm0 NamedList where
  trim (Closure t e) = Closure t e

instance PrintableState (State NamedList) where
  toDState state = do
    h <- collectHeap state
    h' <- convHeap' h
    s' <- convStateRef (ioToRefH h) state
    return (convHeap'' h', convState'' s')

mkClosure :: IsDBEnv t => DBTrim DBTTerm0 -> Environment t -> Closure DBTTerm0 t
mkClosure (Trimmer0 x, t) e = case trimEnv x e of
  (Just e') -> Closure t e'
  Nothing -> error ("mkClosure: " ++ show t ++ "\nEnvironment length: " ++ show (LAM.IsDBEnv.length e))

mark3 :: IsDBEnv t => State t -> IO (Either String (State t))
mark3 (Closure (DBTVar x) e, s) = case lookupI x e of
  Nothing  -> return (Left "Bug: Var: lookup failed")
  (Just p) -> do
    r <- readIORef p
    case r of
      Nothing -> return (Left "Var: black hole")
      (Just c) -> do
        writeIORef p Nothing -- insert black hole
        return (Right (c, H p : s))
mark3 (Closure (DBTLam _ _)   e,   [])      = return (Left "Finished: Lam: stack empty")
mark3 (Closure (DBTLam y e)   env, P p : s) = return (Right (Closure e (cons y p env), s))
mark3 (Closure t@(DBTLam _ _) env, H p : s) = let c = Closure t env in do
  writeIORef p (Just c)
  return (Right (c, s))
mark3 (Closure (DBTApp e x) env, s) = case lookupI x env of
  Nothing  -> return (Left "Bug: App: lookup failed")
  (Just p) -> return (Right (Closure e env, P p : s))
mark3 (Closure t@(DBTLet x e) env, s) = do
  ext <- mapM (\(n, t) -> do r <- newIORef Nothing; return (n, r, t)) x
  let env' = app (fromList (map (\(n, r, t) -> (n, r)) ext)) env
  mapM_ (\(n, r, t) -> writeIORef r (Just (mkClosure t env'))) ext
  return (Right (mkClosure e env', s))

isLAMG :: IsDBEnv t => IsLAM IO String (State t) Term
isLAMG = IsLAM { step = mark3, initS = \t -> (Closure (termToDBTTerm0 t) (fromList []), []) }

isLAM :: IsLAM IO String (State []) Term
isLAM = isLAMG

isLAMN :: IsLAM IO String (State NamedList) Term
isLAMN = isLAMG
