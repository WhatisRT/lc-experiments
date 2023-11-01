module LAMDB2 where

import LAM.Base hiding (HeapPointer, Environment, Stack, State)

import Data.IORef
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Sequence

type HeapPointer = IORef (Maybe (Closure DBTerm Seq))
type Environment = Seq HeapPointer

type Control = DBTerm

type Stack = [Tag HeapPointer]

type Err = String

type State = (Control, Environment, Stack)


mark2 :: State -> IO (Either Err State)
mark2 (Var x , e , s) = case Sequence.lookup x e of
  Nothing  -> return (Left "Bug: Var: lookup failed")
  (Just p) -> do
    r <- readIORef p
    case r of
      Nothing -> return (Left "Var: black hole")
      (Just (Closure t env)) -> do
        writeIORef p Nothing -- insert black hole
        return (Right (t , env , H p : s))
mark2 (Lam _ _     , e , [])        = return (Left "Finished: Lam: stack empty")
mark2 (Lam y e     , env , P p : s) = return (Right (e , p <| env , s))
mark2 (t@(Lam _ _) , env , H p : s) = do
  writeIORef p (Just (Closure t env))
  return (Right (t , env , s))
mark2 (App e x    , env , s) = case Sequence.lookup x env of
  Nothing  -> return (Left "Bug: App: lookup failed")
  (Just p) -> return (Right (e , env , P p : s))
mark2 (t@(Let x e) , env , s) = do
  ext <- mapM (\ (n , t) -> do r <- newIORef Nothing ; return (n , r , t)) x
  let env' = Sequence.fromList (map (\ (n , r , t) -> r) ext) >< env
  mapM_ (\ (n , r , t) -> writeIORef r (Just (Closure t env'))) ext
  return (Right (e , env' , s))


isLAM :: IsLAM IO Err State Term
isLAM = IsLAM { step = mark2, initS = \t -> (toDBTerm id t , Sequence.empty , []) }
