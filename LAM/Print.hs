{-# LANGUAGE BlockArguments #-}
module LAM.Print where

import LAM.Base

import Control.Monad
import Data.IORef
import Data.List
import Data.Text (unpack)
import Data.Void
import System.IO.Unsafe

import Trie.Map (Trie)
import qualified Data.Map as Map
import qualified Trie.Map as Trie

import Addr
import Numeric

instance Show (IORef a) where
  show r = "#" ++ (showHex (unsafeAddr r) "")

unsafeShowIORef :: (Show a) => IORef a -> String
unsafeShowIORef r = unsafePerformIO $ do
  x <- readIORef r
  return ("#" ++ (showHex (unsafeAddr x) "") ++ "(" ++ show x ++ ")")

showClosurePretty
  :: Show a =>
     (Name -> t (r (Maybe (RClosure r Term t))) -> Maybe a)
     -> RClosure r Term t -> String
showClosurePretty lookup (Closure t env) =
  showTermWithCtx absurd (\n -> unpack n ++ "[" ++ (case lookup n env of
                             Nothing  -> "UNKNOWN"
                             (Just x) -> show x) ++ "]") t


instance Show (Closure Term []) where
  show (Closure t env) = "Closure { t = " ++ show t ++ ", env = " ++ show env ++ " }"

instance Show (Closure Term Trie) where
  show = showClosurePretty Trie.lookup

instance Show DClosure where
  show = showClosurePretty Trie.lookup

instance Show PClosure where
  show = showClosurePretty (\n (NamedList e) -> Data.List.lookup n e)

instance Show (Closure DBTerm t) where
  show (Closure t _) = show t

instance {-# OVERLAPS #-} Show (Closure DBTerm NamedList) where
  show (Closure t e) = "Closure { t = " ++ show t ++ ", env = " ++ show e ++ " }"


type Addr = Int

data Ref a = Ref Addr deriving (Eq, Functor, Foldable, Traversable)

instance Show (Ref a) where
  show (Ref r) = show r

convRef :: Ref a -> Ref b
convRef (Ref a) = Ref a

ioRefAddr :: IORef a -> IO Int
ioRefAddr r = unsafeAddr <$> readIORef r

ioToRef :: IORef a -> IO (Ref a)
ioToRef r = Ref <$> ioRefAddr r

ioToRefH :: HeapRefs term t -> IORef (Maybe (Closure term t))
         -> IO (Ref (Maybe (Closure term t)))
ioToRefH h r = case findIndex ((==) r) h of
  Nothing  -> error "BUG: not in heap"
  (Just i) -> return (Ref i)

ioToRefHDebug :: Show (Closure term t) => HeapRefs term t -> IORef (Maybe (Closure term t))
              -> IO (Ref (Maybe (Closure term t)))
ioToRefHDebug h r = case findIndex ((==) r) h of
  Nothing  -> error ("BUG: not in heap: " ++ unsafeShowIORef r ++ "\n\n" ++ intercalate "\n" (map unsafeShowIORef h))
  (Just i) -> return (Ref i)

ioToRefPair :: IORef a -> IO (Ref a, a)
ioToRefPair r = do
  a <- ioRefAddr r
  x <- readIORef r
  return (Ref a, x)

-- ioToRefPairH :: HeapRefs term t -> IORef (Maybe (Closure term t))
--              -> IO (Ref (Maybe (Closure term t)), Maybe (Closure term t))
-- ioToRefPairH h r = case findIndex ((==) r) h of
--   Nothing  -> error "BUG: not in heap"
--   (Just i) -> (Ref i,) <$> readIORef r

convHeap' :: (Traversable t, CanTrim term t)
          => HeapRefs term t -> IO (RHeap term t)
convHeap' h = forM (zip [0..] h)
  (\(i, r) -> readIORef r >>= (\r' -> (Ref i,) <$> traverse (convClosureRef (ioToRefH h) . trim) r'))

convHeap'Debug :: (Traversable t, CanTrim term t, Show (Closure term t))
          => HeapRefs term t -> IO (RHeap term t)
convHeap'Debug h = forM (zip [0..] h)
  (\(i, r) -> readIORef r >>= (\r' -> (Ref i,) <$> traverse (convClosureRef (ioToRefHDebug h) . trim) r'))

convHeap'' :: RState IORef Term Trie -> IO DState
convHeap'' state = do
  h <- collectHeap state
  h' <- convHeap' h
  s <- convStateRef (ioToRefH h) state
  return (h', s)

type RHeap term t = [(RHeapPointer Ref term t, Maybe (RClosure Ref term t))]

instance Eq DClosure where
  (==) (Closure t e) (Closure t' e') = t == t' && e == e'

type DClosure = RClosure Ref Term Trie
type DHeapPointer = RHeapPointer Ref Term Trie
type DEnvironment = REnvironment Ref Term Trie
type DStack = RStack Ref Term Trie
type DHeap = RHeap Term Trie

type DState = (DHeap, RState Ref Term Trie)

type PClosure = RClosure Ref Term NamedList
type PHeapPointer = RHeapPointer Ref Term NamedList
type PEnvironment = REnvironment Ref Term NamedList
type PStack = RStack Ref Term NamedList
type PHeap = RHeap Term NamedList

type PState = (PHeap, RState Ref Term NamedList)

--------------------------------------------------------------------------------
-- Heuristric comparisons
--
-- compare while ignoring all pointers
--------------------------------------------------------------------------------

trimClosure (Closure t (NamedList e)) =
  Closure t $ NamedList $ filter (\(n, _) -> n `elem` freeVars t) e

closureEnvPtrs = (\(Closure _ (NamedList e)) -> map snd e) . trimClosure

trimHeap :: PHeap -> [PHeapPointer] -> PHeap
trimHeap h roots = if roots == closure then restrictedHeap else trimHeap h closure
  where
    closure = nub (roots ++ (concatMap (\(_,x) -> maybe [] closureEnvPtrs x) restrictedHeap))
    restrictedHeap = filter (\(r,_) -> r `elem` roots) h

trimState :: PState -> PState
trimState (h, (c, s)) = (trimHeap h (nub (closureEnvPtrs c ++ map (\case { H x -> x; P x -> x }) s)), (trimClosure c, s))

sortHeap :: PHeap -> PHeap
sortHeap = sortOn (\case { (_,Nothing) -> Nothing; (_, Just (Closure t _)) -> Just t})

heuristicCompTag :: Tag a -> Tag a -> Bool
heuristicCompTag (P _) (P _) = True
heuristicCompTag (H _) (H _) = True
heuristicCompTag _     _     = False

heuristicCompPStack :: PStack -> PStack -> Bool
heuristicCompPStack s s' = length s == length s' && (and $ zipWith heuristicCompTag s s')

heuristicCompPClosure :: PClosure -> PClosure -> Bool
heuristicCompPClosure (Closure t _) (Closure t' _) = t == t'

heuristicCompPHeap :: PHeap -> PHeap -> Bool
heuristicCompPHeap h h' = length h == length h' && (and $ zipWith (curry \case
  ((_, Just c),  (_, Just c')) -> heuristicCompPClosure c c'
  ((_, Nothing), (_, Nothing)) -> True
  (_          , _)             -> False)
                            h h')

heuristicCompPState' :: PState -> PState -> Bool
heuristicCompPState' (h, (c, s)) (h', (c', s')) =
     heuristicCompPHeap (sortHeap h) (sortHeap h')
  && heuristicCompPClosure c c'
  && heuristicCompPStack s s'

heuristicCompPState :: PState -> PState -> Bool
heuristicCompPState s s' = heuristicCompPState' (trimState s) (trimState s')

--------------------------------------------------------------------------------

class PrintableState a where
  toDState :: a -> IO DState
  toPrintableState :: a -> IO PState
  toPrintableState s = (simpHeapAddrs . toPStateD) <$> toDState s

printTrace :: PrintableState s => IsLAM IO e s t -> t -> IO ()
printTrace l t = print =<< traverse toPrintableState =<< runTrace' l t

instance PrintableState State where
  toDState s@(Closure _ e, _) = convHeap'' s

toPPtrD :: DHeapPointer -> PHeapPointer
toPPtrD = convRef

toPEnvD :: DEnvironment -> PEnvironment
toPEnvD e = NamedList $ (\(n , r) -> (n, toPPtrD r)) <$> Map.toList e

toPClosureD :: DClosure -> PClosure
toPClosureD (Closure t env) = Closure t $ toPEnvD env

toPStackD :: DStack -> PStack
toPStackD = fmap (fmap toPPtrD)

toPHeapD :: DHeap -> PHeap
toPHeapD = map (\(Ref a, c) -> (Ref a, toPClosureD <$> c))

toPStateD :: DState -> PState
toPStateD (h, (Closure t e, s)) = (toPHeapD h, (Closure t (toPEnvD e), toPStackD s))



simpHeapAddrs :: PState -> PState
simpHeapAddrs ps@(e, (c, s)) = (map (\(p, c) -> (mapAddr p, fmap simpClosure c)) e
                             , (simpClosure c
                             , map (fmap mapAddr) s))
  where
    heapAddrs :: [PHeapPointer]
    heapAddrs = nub $ map fst e ++ map (\case { (P a) -> a; (H a) -> a }) s

    mapAddr :: PHeapPointer -> PHeapPointer
    mapAddr ptr = maybe (error ("simpHeapAddrs: " ++ show ptr ++ "\n" ++ show ps)) Ref $
      flip elemIndex heapAddrs ptr

    simpClosure :: PClosure -> PClosure
    simpClosure (Closure t (NamedList env)) =
      Closure t $ NamedList $ map (\(a, b) -> (a, mapAddr b)) env
