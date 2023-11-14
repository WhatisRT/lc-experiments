-- | This module contains all sorts of general definitions for working with terms
module LAM.Base
  ( module LAM.Types.BV
  , module LAM.Types.Generic
  , module LAM.Types.Pure
  , freeIxs, appT
  , IsNamedEnv(..), NamedList(..), RClosure(..), Tag(..)
  , RState, State, RStack, REnvironment, RHeapPointer, HeapRefs, Closure
  , freeVars, convStateRef, convClosureRef, withFix, toTerm, unsafeLookupNs, mapFree, collectHeap) where

import Control.Monad
import Data.IORef
import Data.List
import Data.Text (Text, pack, unpack)
import LAM.Types.BV
import LAM.Types.Generic
import LAM.Types.Pure
import Text.Parsec hiding (State)
import Trie.Map (Trie)
import qualified LC.Base as LC
import qualified Trie.Map as Trie

-- isClosed :: Term -> Bool
-- isClosed = null . freeVars

-- | An environment
class IsNamedEnv t where
  eToList   :: t a -> [(Name, a)]
  eFromList :: [(Name, a)] -> t a
  eLookup   :: Name -> t a -> Maybe a
  eLookup n e = Data.List.lookup n (eToList e)

-- If we don't have names, we invent some
instance IsNamedEnv [] where
  eToList = zip (map (\x -> pack $ "DB" ++ show (x :: Integer)) [0..])
  eFromList = map snd

instance IsNamedEnv NamedList where
  eToList (NamedList l) = l
  eFromList l = NamedList l

instance IsNamedEnv Trie where
  eToList = Trie.toList
  eFromList = Trie.fromList
  eLookup = Trie.lookup

-- | A basic environment for DeBruijn terms, including names for
-- converting to a named representation.

newtype NamedList a = NamedList [(Name, a)]
  deriving (Functor, Foldable, Traversable, Show)

-- | Tags for storing things on the stack.
data Tag a = P a | H a
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Closure with a pointer type @r@.
data RClosure r term t = Closure { t :: term, env :: t (RHeapPointer r term t) }

-- | Pointer to a closure or black hole
type RHeapPointer r term t = r (Maybe (RClosure r term t))
-- | An environment is a container of heap pointers. Does not specify
-- how to index into the environment, so this works for named or
-- DeBruijn.
type REnvironment r term t = t (RHeapPointer r term t)
-- | Since we only ever interact with the stack via the top element,
-- this can just be a list.
type RStack r term t = [Tag (RHeapPointer r term t)]

-- | The state is a pair of a closure and a stack.
type RState r term t = (RClosure r term t, RStack r term t)

-- | The most common pointer type is 'IORef'.
type Closure term t = RClosure IORef term t
-- type HeapPointer = RHeapPointer IORef Term Trie
-- type Environment = REnvironment IORef Term Trie
-- type Stack = RStack IORef Term Trie

-- | Same as above.
type State = RState IORef Term Trie

-- * Converting pointer types
-- Usually, we want to convert from 'IORef' to some type that we can
-- work with more easily.

convPtrRef :: (Monad m, Traversable t, Traversable r')
           => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
           -> RHeapPointer r term t -> m (RHeapPointer r' term t)
convPtrRef f p = f p >>= traverse (traverse (convClosureRef f))

convEnvRef :: (Monad m, Traversable t, Traversable r')
           => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
           -> REnvironment r term t -> m (REnvironment r' term t)
convEnvRef f = traverse (convPtrRef f)

-- | Convert the pointer type in a closure.
convClosureRef :: (Monad m, Traversable t, Traversable r')
               => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
               -> RClosure r term t -> m (RClosure r' term t)
convClosureRef f (Closure t e) = Closure t <$> convEnvRef f e

-- | Convert the pointer type in a state.
convStateRef :: (Monad m, Traversable t, Traversable r')
             => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
             -> RState r term t -> m (RState r' term t)
convStateRef f (c, s) = do
  c' <- convClosureRef f c
  s' <- traverse (traverse (convPtrRef f)) s
  return (c', s')



-- mapC :: (term1 -> term2)
--      -> (t1 (r (Maybe (RClosure r term1 t1))) -> t2 (r (Maybe (RClosure r term2 t2))))
--      -> RClosure r term1 t1 -> RClosure r term2 t2
-- mapC f g (Closure t env) = Closure (f t) (g env)

-- ** Heap functions
-- This is used to extract the heap and work with it more nicely.

-- | A type for collecting heap pointers.
type HeapRefs term t = [IORef (Maybe (RClosure IORef term t))]

-- | Resolve all heap pointers (i.e. 'IORef's) of a 'RState'.
collectHeap :: (Traversable t) => RState IORef term t -> IO (HeapRefs term t)
collectHeap (c, s) = addEnvironment [] (env c) >>= flip addStack s
  where
    addClosure :: (Traversable t)
               => IORef (Maybe (Closure term t)) -> IO (HeapRefs term t) -> IO (HeapRefs term t)
    addClosure c' env' = do
      env <- env'
      if c' `elem` env
        then return env -- if an address is in env, all transitively reachable addresses are as well
        else let env' = c' : env in
          maybe (return env') ((\(Closure _ e) -> addEnvironment env' e)) =<< readIORef c'

    addEnvironment :: (Traversable t)
                   => HeapRefs term t -> REnvironment IORef term t -> IO (HeapRefs term t)
    addEnvironment env e = foldr addClosure (return env) e

    addStack :: (Traversable t)
             => HeapRefs term t -> RStack IORef term t -> IO (HeapRefs term t)
    addStack env s = foldr (\case { H x -> addClosure x ; P x -> addClosure x }) (return env) s

-- ** General-purpose

-- | Generate a name that doesn't appear in a 'Term'.
freshName :: String -> Term -> Name
freshName n t = pack (n ++ show (helper t))
  where
    parseNat :: Parsec Text () Integer
    parseNat = do
      first <- oneOf "123456789"
      rest <- many (oneOf "0123456789")
      return (read (first : rest))

    parseN :: Text -> Maybe Integer
    parseN s = case parse (string n >> parseNat) "" s of
      (Left _)  -> Nothing
      (Right i) -> Just i

    toNsuc :: Name -> Integer
    toNsuc n' = case parseN n' of
      (Just x) -> succ x
      Nothing  -> 0

    helper :: Term -> Integer
    helper (Var x)   = toNsuc x
    helper (Lam _ t) = helper t
    helper (App t x) = max (helper t) (toNsuc x)
    helper (Let x t) = foldl max (helper t) (map (helper . snd) x)

-- | Emulate application.
appT :: Term -> Term -> Term
appT t (Var x) = App t x
appT t t'      = let x = freshName "a" t in Let [(x , t')] (App t x)

-- | Convert a general lambda term to a representation for our
-- abstract machines.
toTerm :: LC.Term -> Term
toTerm (LC.Var n) = Var n
toTerm (LC.Lam n t) = Lam n (toTerm t)
toTerm (LC.App t t') = appT (toTerm t) (toTerm t')

-- | Add a fix point operator to a term.
withFix :: Term -> Term
withFix t = Let [ ("fix" , Lam "f" (Let [ ("fixf" , App (Var "fix") "f") ] (App (Var "f") "fixf"))) ] t

-- | The free variables of a term.
--
-- prop> freeVars (λ x. t) = freeVars t \ [x]
freeVars :: Term -> [Name]
freeVars = nub . go []
  where
    addVar ctx x = if x `elem` ctx then [] else [x]

    go :: [Name] -> Term -> [Name]
    go ctx (Var x)   = addVar ctx x
    go ctx (Lam x t) = go (x:ctx) t
    go ctx (App t x) = go ctx t ++ addVar ctx x
    go ctx (Let x t) = let ctx' = map fst x ++ ctx in
      concatMap (go ctx') (map snd x) ++ go ctx' t

-- | DeBruijn version of 'freeVars'.
--
-- prop> length (freeIxs (toDBTerm t)) = length (freeVars t)
-- prop> length ctx = maximum (freeIxs t) + 1 => freeVars (fromDBTermCtx ctx t) = ctx
freeIxs :: DBTerm -> [Int]
freeIxs = nub . sort . helper
  where
    strengthenBy :: Int -> [Int] -> [Int]
    strengthenBy n l = map (\k -> k-n) (filter (\x -> not (elem x [0..n-1])) l)

    helper :: DBTerm -> [Int]
    helper (Var i)   = [i]
    helper (Lam _ t) = strengthenBy 1 (helper t)
    helper (App t i) = i : helper t
    helper (Let x t) = strengthenBy (length x) (concatMap (\(_,t) -> helper t) x ++ helper t)

-- | Apply some transformation to the free variables.
--
-- prop> map f (freeVars t) = freeVars (mapFree t)
mapFree :: (Int -> Int) -> DBTerm -> DBTerm
mapFree f = go 0
  where
    modI ctx i = if i < ctx then i else (f (i - ctx)) + ctx

    go :: Int -> DBTerm -> DBTerm
    go ctx (Var i)   = Var (modI ctx i)
    go ctx (Lam n t) = Lam n (go (ctx+1) t)
    go ctx (App t i) = App (go ctx t) (modI ctx i)
    go ctx (Let x t) = let ctx' = ctx+length x in
      Let (map (\(n, t') -> (n, go ctx' t')) x) (go ctx' t)

--------------------------------------------------------------------------------
-- Manage environments

lookupNs :: [Name] -> Trie a -> Either Name [(Name, a)]
lookupNs vars e =
  forM vars $ \n -> case Trie.lookup n e of
    (Just r) -> return (n, r)
    Nothing -> Left n

-- | Lookup a subset of a trie.
unsafeLookupNs :: [Name] -> Trie a -> [(Name, a)]
unsafeLookupNs vars e = case lookupNs vars e of
  (Left n) -> error ("unsafeLookupNs: " ++ unpack n)
  (Right l) -> l
