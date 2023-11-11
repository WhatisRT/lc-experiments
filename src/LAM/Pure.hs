-- | Pure versions of abstract machine states.
--
-- These hold the entire state, instead of needing an IO context to
-- fetch data from the heap.
module LAM.Pure
  ( ToPureState(..), PState, PState', IsNamedEnv(..), RHeap, Ref
  , simpHeapAddrs, heuristicCompState, heuristicCompPState, trimState, toPureStateGen)
where

import LAM.Base
import LAM.IsLAM
import LAM.CanTrim

import Control.Monad
import Data.Functor.Classes
import Data.IORef
import Data.List
import Data.Text (unpack)
import Data.Void

import Trie.Map (Trie)
import qualified Data.Map as Map
import qualified Trie.Map as Trie

import Addr (unsafeAddr)
import Numeric

-- | Addresses
type Addr = Int

-- | The address pointing to a value of type @a@. We want to convert
-- an 'IORef' to this.
data Ref a = Ref Addr deriving (Eq, Functor, Foldable, Traversable)

instance Show (Ref a) where
  show (Ref r) = show r

convRef :: Ref a -> Ref b
convRef (Ref a) = Ref a

ioToRefH :: HeapRefs term t -> IORef (Maybe (Closure term t))
         -> IO (Ref (Maybe (Closure term t)))
ioToRefH h r = case findIndex ((==) r) h of
  Nothing  -> error "BUG: not in heap"
  (Just i) -> return (Ref i)

--------------------------------------------------------------------------------
-- Pure states & friends

-- | A list representing the heap. We extract this from an abstract
-- machine to get a pure value we can manipulate freely.
type RHeap term t = [(RHeapPointer Ref term t, Maybe (RClosure Ref term t))]

type PClosure t = RClosure Ref Term t
type PHeapPointer t = RHeapPointer Ref Term t
type PEnvironment t = REnvironment Ref Term t
type PStack t = RStack Ref Term t

-- | A pure heap.
type PHeap t = RHeap Term t

-- | Pure state, but without heap
type PState' t = RState Ref Term t

-- | Pure state, i.e. a state that includes the heap.
type PState t = (RHeap Term t, PState' t)

--------------------------------------------------------------------------------
-- Conversions between various pure states

convClosure :: (IsNamedEnv t1, IsNamedEnv t2)
             => (t -> DBTerm) -> RClosure Ref t t1 -> PClosure t2
convClosure f (Closure t e') = let e = eToList e' in
  Closure (fromDBTermCtx id (map fst e) $ f t)
          (eFromList $ reverse $ map (\(n, r) -> (n, convRef r)) e)

convHeap :: (IsNamedEnv t1, IsNamedEnv t2)
         => (t -> DBTerm) -> RHeap t t1 -> PHeap t2
convHeap f h = map (\(Ref a, c) -> (Ref a, fmap (convClosure f) c)) h

convState' :: (IsNamedEnv t1, IsNamedEnv t2)
           => (t -> DBTerm) -> RState Ref t t1 -> PState' t2
convState' f (c, s) = (convClosure f c, map (fmap convRef) s)

convState :: (Traversable t, CanTrim term t, IsNamedEnv t')
  => (RHeap term t -> PHeap t') -> (RState Ref term t -> PState' t')
  -> RState IORef term t -> IO (PState t')
convState f g state = do
  h <- collectHeap state
  liftM2 (,) (f <$> convHeap' h) (g <$> convStateRef (ioToRefH h) state)
  where
    convHeap' :: (Traversable t, CanTrim term t) => HeapRefs term t -> IO (RHeap term t)
    convHeap' h = forM (zip [0..] h)
      (\(i, r) -> readIORef r >>= (\r' -> (Ref i,) <$> traverse (convClosureRef (ioToRefH h) . trim) r'))

--------------------------------------------------------------------------------

showClosurePretty
  :: Show a =>
     (Name -> t (r (Maybe (RClosure r Term t))) -> Maybe a)
     -> RClosure r Term t -> String
showClosurePretty lookup (Closure t env) =
  showTermWithCtx absurd (\n -> unpack n ++ "[" ++ (case lookup n env of
                             Nothing  -> "UNKNOWN"
                             (Just x) -> show x) ++ "]") t

instance Show (IORef a) where
  show r = "#" ++ (showHex (unsafeAddr r) "")

instance IsNamedEnv t => Show (PClosure t) where
  show = showClosurePretty eLookup

instance Show (Closure Term Trie) where
  show = showClosurePretty Trie.lookup

instance Show (Closure DBTerm t) where
  show (Closure t _) = show t

--------------------------------------------------------------------------------
-- ToPureState class

-- | A class for printing abstract machine states.
class IsNamedEnv t => ToPureState a t where
  toPureState :: a -> IO (PState t)

-- | Generic function to write 'ToPureState' classes.
toPureStateGen :: (CanTrim t t1, Traversable t1, IsNamedEnv t1, IsNamedEnv t2)
               => (t -> DBTerm) -> RState IORef t t1 -> IO (PState t2)
toPureStateGen f = convState (convHeap f) (convState' f)

instance IsNamedEnv t => ToPureState (PState t) t where
  toPureState = return

instance (Traversable t1, CanTrim Term t1, IsNamedEnv t1, IsNamedEnv t2)
  => ToPureState (RState IORef Term t1) t2 where
  toPureState s@(Closure _ e, _) = toPureState =<< convState id id s

instance (IsNamedEnv t1, IsNamedEnv t2) => ToPureState (PState t1) t2 where
  toPureState = return . toPStateD
    where
      toPPtrD :: (IsNamedEnv t1, IsNamedEnv t2) => PHeapPointer t1 -> PHeapPointer t2
      toPPtrD = convRef

      toPEnvD :: (IsNamedEnv t1, IsNamedEnv t2) => PEnvironment t1 -> PEnvironment t2
      toPEnvD e = eFromList $ (\(n , r) -> (n, toPPtrD r)) <$> eToList e

      toPClosureD :: (IsNamedEnv t1, IsNamedEnv t2) => PClosure t1 -> PClosure t2
      toPClosureD (Closure t env) = Closure t $ toPEnvD env

      toPStackD :: (IsNamedEnv t1, IsNamedEnv t2) => PStack t1 -> PStack t2
      toPStackD = fmap (fmap toPPtrD)

      toPHeapD :: (IsNamedEnv t1, IsNamedEnv t2) => PHeap t1 -> PHeap t2
      toPHeapD = map (\(Ref a, c) -> (Ref a, toPClosureD <$> c))

      toPStateD :: (IsNamedEnv t1, IsNamedEnv t2) => PState t1 -> PState t2
      toPStateD (h, (Closure t e, s)) = (toPHeapD h, (Closure t (toPEnvD e), toPStackD s))

--------------------------------------------------------------------------------
-- Heuristric comparisons
--
-- compare while ignoring all pointers
--------------------------------------------------------------------------------

trimClosure :: IsNamedEnv t => RClosure Ref Term t -> RClosure Ref Term t
trimClosure (Closure t e) =
  Closure t $ eFromList $ filter (\(n, _) -> n `elem` freeVars t) $ eToList e

closureEnvPtrs :: IsNamedEnv t => RClosure Ref Term t -> [RHeapPointer Ref Term t]
closureEnvPtrs = (\(Closure _ e) -> map snd $ eToList e) . trimClosure

trimHeap :: IsNamedEnv t => PHeap t -> [PHeapPointer t] -> PHeap t
trimHeap h roots = if roots == closure then restrictedHeap else trimHeap h closure
  where
    closure = nub (roots ++ (concatMap (\(_,x) -> maybe [] closureEnvPtrs x) restrictedHeap))
    restrictedHeap = filter (\(r,_) -> r `elem` roots) h

-- | Removed unused references from 'PState
trimState :: IsNamedEnv t => PState t -> PState t
trimState (h, (c, s)) =
  (trimHeap h (nub (closureEnvPtrs c ++ map (\case { H x -> x; P x -> x }) s)), (trimClosure c, s))

sortHeap :: PHeap t -> PHeap t
sortHeap = sortOn (\case { (_,Nothing) -> Nothing; (_, Just (Closure t _)) -> Just t})

heuristicCompTag :: Tag a -> Tag a -> Bool
heuristicCompTag (P _) (P _) = True
heuristicCompTag (H _) (H _) = True
heuristicCompTag _     _     = False

heuristicCompPStack :: PStack t -> PStack t -> Bool
heuristicCompPStack = liftEq heuristicCompTag

heuristicCompPClosure :: PClosure t -> PClosure t -> Bool
heuristicCompPClosure (Closure t _) (Closure t' _) = t == t'

heuristicCompPHeap :: PHeap t -> PHeap t -> Bool
heuristicCompPHeap = liftEq (\(_,x) (_,y) -> liftEq heuristicCompPClosure x y)

heuristicCompPState' :: PState t -> PState t -> Bool
heuristicCompPState' (h, (c, s)) (h', (c', s')) =
     heuristicCompPHeap (sortHeap h) (sortHeap h')
  && heuristicCompPClosure c c'
  && heuristicCompPStack s s'

-- | Heuristic equality for 'PState. This doesn't properly follow
-- pointers, but it should be very difficult to create two states that
-- this test equates but aren't actually equal.
--
-- prop> heuristicCompPState s1 s2 = false => s1 /= s2
heuristicCompPState :: IsNamedEnv t => PState t -> PState t -> Bool
heuristicCompPState s s' = heuristicCompPState' (trimState s) (trimState s')

-- | Heuristic equality for 'ToPureState's. This doesn't properly
-- follow pointers, but it should be very difficult to create two
-- states that this test equates but aren't actually equal.
--
-- prop> heuristicCompState s1 s2 = false => s1 /= s2
heuristicCompState :: (ToPureState s1 Trie, ToPureState s2 Trie) => s1 -> s2 -> IO Bool
heuristicCompState s s' =
  liftM2 heuristicCompPState (toPureState s) (toPureState s' :: IO (PState Trie))

--------------------------------------------------------------------------------
-- Other

-- | Replace actual heap addresses by small integers to make it easier
-- to read the output.
simpHeapAddrs :: IsNamedEnv t => PState t -> PState t
simpHeapAddrs ps@(e, (c, s)) = (map (\(p, c) -> (mapAddr p, fmap simpClosure c)) e
                             , (simpClosure c
                             , map (fmap mapAddr) s))
  where
    heapAddrs = nub $ map fst e ++ map (\case { (P a) -> a; (H a) -> a }) s

    mapAddr ptr = maybe (error ("simpHeapAddrs: " ++ show ptr ++ "\n" ++ show ps)) Ref $
      flip elemIndex heapAddrs ptr

    simpClosure (Closure t e) = let env = eToList e in
      Closure t $ eFromList $ map (\(a, b) -> (a, mapAddr b)) env
