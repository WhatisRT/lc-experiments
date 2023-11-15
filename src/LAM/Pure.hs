-- | Pure versions of abstract machine states.
--
-- These hold the entire state, instead of needing an IO context to
-- fetch data from the heap.
module LAM.Pure
  ( ToPureState(..), PState, PState', IsNamedEnv(..), RHeap, Ref
  , simpHeapAddrs, heuristicCompState, heuristicCompPState, trimState, toPureStateGen
  , stateToTerm, runHnf, runHnfPrint, runHnfPrintTrace )
where

import LAM.Base
import LAM.IsLAM
import LAM.CanTrim

import Control.Monad
import Data.Functor.Classes
import Data.IORef
import Data.List
import Data.Maybe
import Data.Text (pack, unpack)
import Data.Tuple
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

-- | Like 'RHeap', but specialized to 'Term' and including name suggestions.
type NHeap t = [([Name], PHeapPointer t, Maybe (PClosure t))]

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
-- Extract terms

addNames :: IsNamedEnv t => PHeap t -> PClosure t -> NHeap t
addNames h c = map (\(p, v) -> (concatMap (findNames p) (c:catMaybes (map snd h)), p, v)) h
  where
    findNames :: IsNamedEnv t => PHeapPointer t -> PClosure t -> [Name]
    findNames p (Closure _ e) = map fst $ filter (\(n, p') -> p == p') $ eToList e

selectNames :: NHeap t -> [(PHeapPointer t, Name)]
selectNames = go []
  where go :: [Name] -> NHeap t -> [(PHeapPointer t, Name)]
        go acc [] = []
        go acc ((ns, p, _):rest) =
          let candidates = ns ++ [pack (unpack (head ns) ++ show k) | k <- ([0..] :: [Int])]
              n = case filter (\n' -> not (n' `elem` acc)) candidates of
                    []    -> error "Bug: empty list of candidates"
                    (n:_) -> n
          in (p,n):go (n:acc) rest

getSelectedName :: IsNamedEnv t => [(PHeapPointer t, Name)] -> t (PHeapPointer t) -> Name -> Name
getSelectedName m e n = case eLookup n e of
  Nothing -> error ("Bug: environment lookup failed: " ++ show n)
  (Just p) -> case lookup p m of
    Nothing -> error "Bug: selection lookup failed"
    (Just n) -> n

mapFreeNamed :: (Name -> Name) -> Term -> Term
mapFreeNamed f = go []
  where
    rename ctx n = if n `elem` ctx then n else f n

    go ctx (Var x)   = Var (rename ctx x)
    go ctx (Lam x t) = Lam x (go (x:ctx) t)
    go ctx (App t x) = App (go ctx t) (rename ctx x)
    go ctx (Let x t) = let ctx' = map fst x ++ ctx in
      Let (map (\(n,t') -> (n,go ctx' t')) x) (go ctx' t)

getHeapClosure :: IsNamedEnv t => PHeap t -> [(PHeapPointer t, Name)] -> Name -> PClosure t
getHeapClosure h m n = case lookup n (map swap m) of
  Nothing -> error "Bug: selection lookup failed"
  (Just p) -> case lookup p h of
    Nothing -> error "Bug: heap lookup failed"
    (Just Nothing) -> error "Bug: black hole"
    (Just (Just c)) -> c

closureToTerm :: IsNamedEnv t => PHeap t -> [(PHeapPointer t, Name)] -> PClosure t -> Term
closureToTerm h m (Closure t e) = let
    mapT = mapFreeNamed (getSelectedName m e)
    t' = mapT t
    ns = freeVars t'
  in if null ns then t'
  else Let (map (\n -> (n, case getHeapClosure h m n of (Closure t _) -> mapT t)) ns) t'

overrideHeap h (p, c) = (p, c) : filter (\(p',_) -> p /= p') h

stateToTerm :: IsNamedEnv t => PState t -> Term
stateToTerm (h, (c, [])) = closureToTerm h (selectNames (addNames h c)) c
stateToTerm (h, (Closure t e, P p@(Ref a) : s)) = case lookup p h of
  ((Just (Just c))) -> let n = "addr" ++ show a
    in stateToTerm (h, (Closure (App t (pack n)) (addToEnv (pack n) p e), s))
  _                 -> error "Bug: Black hole or not in heap"
stateToTerm (h, (c          , H p : s)) =
  stateToTerm (overrideHeap h (p, Just c), (c, s))

stateToTerm' :: ToPureState s Trie => s -> IO Term
stateToTerm' s = stateToTerm <$> (toPureState s :: IO (PState Trie))

runHnf :: ToPureState s Trie => IsLAM IO e s Term -> Term -> IO Term
runHnf l = evalHnf l stateToTerm'

runHnfPrint :: ToPureState s Trie => IsLAM IO e s Term -> Term -> IO ()
runHnfPrint l t = runHnf l t >>= print

runHnfPrintTrace :: ToPureState s Trie => IsLAM IO e s Term -> Term -> IO ()
runHnfPrintTrace l t = runTrace l t >>= traverse stateToTerm' >>= print

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
