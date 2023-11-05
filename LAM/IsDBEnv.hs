module LAM.IsDBEnv where

import Data.IORef
import Data.Text (pack)
import Data.Void
import LAM.Base hiding (HeapPointer, Environment, Stack, State)
import Trie.Map (Trie)
import Util
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
  length = undefined
  cons _ = (<|)
  uncons = undefined
  app = (><)
  lookupI = Sequence.lookup

instance IsDBEnv Vector where
  fromList = Vec.fromList . map snd
  length = undefined
  cons _ = Vec.cons
  uncons = undefined
  app = (Vec.++)
  lookupI = flip (Vec.!?)



toClosure :: IsDBEnv t => Trie (RHeapPointer r DBTerm t) -> Term -> RClosure r DBTerm t
toClosure e t = let vars = freeVars t in
  Closure (toDBTermCtx id vars t) (fromList (unsafeLookupNs vars e))

addToEnv :: IsDBEnv t => Name -> Term -> Trie (RHeapPointer IORef DBTerm t)
         -> IO (Trie (RHeapPointer IORef DBTerm t))
addToEnv n t e = do
  r <- newIORef (Just $ toClosure e t)
  return $ Trie.insert n r e
