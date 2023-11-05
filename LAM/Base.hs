{-# LANGUAGE UndecidableInstances, LambdaCase, OverloadedStrings, AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies, TypeFamilies, PatternSynonyms, StandaloneDeriving #-}
module LAM.Base where

import Control.Monad
import Data.IORef
import Data.List
import Data.Text (Text, pack, unpack)
import Data.Void
import GHC.Generics
import Text.Parsec
import Trie.Map (Trie)
import qualified Trie.Map as Trie
import Util

import qualified Data.Map as Map
import qualified LC.Base as LC

--------------------------------------------------------------------------------

type Name = Text

type family XVar a
type family XLet a
type family XExt a

data ETerm d
  = Var (XVar d)
  | Lam Name (ETerm d)
  | App (ETerm d) (XVar d)
  | XLet (XLet d) [(Name, ETerm d)] (ETerm d)
  | Ext !(XExt d) -- strictness makes the pattern complete when this is empty
  deriving Generic

-- This is a lie, but the ones below don't work
{-# COMPLETE Var, Lam, App, Let, Ext #-}

pattern Let :: (XLet d ~ ()) => [(Name, ETerm d)] -> ETerm d -> ETerm d
pattern Let x t = XLet () x t

deriving instance (Eq (XVar a), Eq (XLet a), Eq (XExt a)) => Eq (ETerm a)
deriving instance (Ord (XVar a), Ord (XLet a), Ord (XExt a)) => Ord (ETerm a)

data Base
type instance XVar Base = Name
type instance XLet Base = ()
type instance XExt Base = Void

data DB
type instance XVar DB = Int
type instance XLet DB = ()
type instance XExt DB = Void

data BVCtrs = CstB Int | OpPB BVTerm BVTerm | OPrB BVTerm

pattern Cst :: (XExt d ~ BVCtrs) => Int -> ETerm d
pattern Cst x = Ext (CstB x)

pattern OpP :: (XExt d ~ BVCtrs) => BVTerm -> BVTerm -> ETerm d
pattern OpP t t' = Ext (OpPB t t')

pattern OPr :: (XExt d ~ BVCtrs) => BVTerm -> ETerm d
pattern OPr t = Ext (OPrB t)

data BVDBCtrs = CstDBBV Int | RetDBBV | OpPDBBV | OPrDBBV
  | CseDBBV BVDBTerm BVDBTerm -- case e of e', single constructor

pattern CstDB :: (XExt d ~ BVDBCtrs) => Int -> ETerm d
pattern CstDB x = Ext (CstDBBV x)

pattern RetDB :: (XExt d ~ BVDBCtrs) => ETerm d
pattern RetDB = Ext RetDBBV

pattern OpPDB :: (XExt d ~ BVDBCtrs) => ETerm d
pattern OpPDB = Ext OpPDBBV

pattern OPrDB :: (XExt d ~ BVDBCtrs) => ETerm d
pattern OPrDB = Ext OPrDBBV

pattern CseDB :: (XExt d ~ BVDBCtrs) => BVDBTerm -> BVDBTerm -> ETerm d
pattern CseDB t t' = Ext (CseDBBV t t')

convBVCtrs :: BVCtrs -> BVDBCtrs
convBVCtrs (CstB x)    = CstDBBV x
convBVCtrs (OpPB t t') = CseDBBV (toDB t) (Ext (CseDBBV (toDB t') OpPDB))
  where toDB = toDBTerm convBVCtrs
convBVCtrs (OPrB t)    = CseDBBV (toDB t) OPrDB
  where toDB = toDBTerm convBVCtrs

convBVCtrs' :: BVDBCtrs -> BVCtrs
convBVCtrs' (CstDBBV x) = CstB x

bvTest :: BVTerm
bvTest = OPr (OpP (Cst 1) (Cst 2))

data BV
type instance XVar BV = Name
type instance XLet BV = ()
type instance XExt BV = BVCtrs

data BVDB
type instance XVar BVDB = Int
type instance XLet BVDB = ()
type instance XExt BVDB = BVDBCtrs

type Term = ETerm Base
type DBTerm = ETerm DB
type BVTerm = ETerm BV
type BVDBTerm = ETerm BVDB


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

isClosed :: Term -> Bool
isClosed = null . freeVars

-- special function to show free variables
showTermWithCtx :: (XVar d ~ Name, XLet d ~ ()) => (XExt d -> String) -> (Name -> String) -> ETerm d -> String
showTermWithCtx f showFree = go [] f
  where
    showVar ctx x = if x `elem` ctx then unpack x else showFree x

    go :: (XVar d ~ Name, XLet d ~ ()) => [Name] -> (XExt d -> String) -> ETerm d -> String
    go ctx f (Var x)   = showVar ctx x
    go ctx f (Lam x t) = "λ " ++ unpack x ++ ". " ++ go (x:ctx) f t
    go ctx f (App t x) = "(" ++ go ctx f t ++ " " ++ showVar ctx x ++ ")"
    go ctx f (Let x t) = let ctx' = map fst x ++ ctx in
      "let " ++ concat (intersperse "; " (map (\(n, t) -> unpack n ++ " = " ++ go ctx' f t) x))
      ++ " in " ++ go ctx' f t
    go ctx f (Ext x) = f x

instance Show Term where
  show = showTermWithCtx absurd unpack

instance Show BVCtrs where
  show (CstB x)    = show x
  show (OpPB t t') = show t ++ " + " ++ show t'
  show (OPrB t)    = "print " ++ show t

instance Show BVTerm where
  show = showTermWithCtx show unpack

newtype NamedList a = NamedList [(Name, a)]
  deriving (Functor, Foldable, Traversable, Show)

data Tag a = P a | H a
  deriving (Eq, Show, Functor, Foldable, Traversable)

data RClosure r term t = Closure { t :: term, env :: t (r (Maybe (RClosure r term t))) }

type RHeapPointer r term t = r (Maybe (RClosure r term t))
type REnvironment r term t = t (RHeapPointer r term t)
type RStack r term t = [Tag (RHeapPointer r term t)]

type RState r term t = (RClosure r term t, RStack r term t)

type Closure term t = RClosure IORef term t
type HeapPointer = RHeapPointer IORef Term Trie
type Environment = REnvironment IORef Term Trie
type Stack = RStack IORef Term Trie

type State = RState IORef Term Trie

--------------------------------------------------------------------------------
-- Manage environments

lookupNs :: [Name] -> Trie a -> Either Name [(Name, a)]
lookupNs vars e =
  forM vars $ \n -> case Trie.lookup n e of
    (Just r) -> return (n, r)
    Nothing -> Left n

unsafeLookupNs :: [Name] -> Trie a -> [(Name, a)]
unsafeLookupNs vars e = case lookupNs vars e of
  (Left n) -> error ("unsafeLookupNs: " ++ unpack n)
  (Right l) -> l

convClosureRef :: (Monad m, Traversable t, Traversable r')
               => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
               -> RClosure r term t -> m (RClosure r' term t)
convClosureRef f (Closure t e) = Closure t <$> convEnvRef f e

convPtrRef :: (Monad m, Traversable t, Traversable r')
           => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
           -> RHeapPointer r term t -> m (RHeapPointer r' term t)
convPtrRef f p = f p >>= traverse (traverse (convClosureRef f))

convEnvRef :: (Monad m, Traversable t, Traversable r')
           => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
           -> REnvironment r term t -> m (REnvironment r' term t)
convEnvRef f = traverse (convPtrRef f)

convStateRef :: (Monad m, Traversable t, Traversable r')
             => (r (Maybe (RClosure r term t)) -> m (r' (Maybe (RClosure r term t))))
             -> RState r term t -> m (RState r' term t)
convStateRef f (c, s) = do
  c' <- convClosureRef f c
  s' <- traverse (traverse (convPtrRef f)) s
  return (c', s')



mapC :: (term1 -> term2)
     -> (t1 (r (Maybe (RClosure r term1 t1))) -> t2 (r (Maybe (RClosure r term2 t2))))
     -> RClosure r term1 t1 -> RClosure r term2 t2
mapC f g (Closure t env) = Closure (f t) (g env)

type HeapRefs term t = [IORef (Maybe (RClosure IORef term t))]

class CanTrim term t where
  trim :: Closure term t -> Closure term t

instance CanTrim Term Trie where
  trim (Closure t e) = Closure t $ Map.filterWithKey (\n _ -> n `elem` freeVars t) e

instance CanTrim Term NamedList where
  trim (Closure t (NamedList e)) = Closure t $ NamedList $ filter (\(n, _) -> n `elem` freeVars t) e

instance CanTrim DBTerm NamedList where
  trim (Closure t (NamedList e)) = let free = freeIxs t in
    Closure (mapFree (\i -> maybe undefined id $ findIndex (i ==) free) t) $
      NamedList [e !! x | x <- free]


collectHeap :: (Traversable t, CanTrim term t) => RState IORef term t -> IO (HeapRefs term t)
collectHeap (c, s) = addEnvironment [] (env c) >>= flip addStack s
  where
    addClosure :: (Traversable t, CanTrim term t)
               => IORef (Maybe (Closure term t)) -> IO (HeapRefs term t) -> IO (HeapRefs term t)
    addClosure c' env' = do
      env <- env'
      if c' `elem` env
        then return env -- if an address is in env, all transitively reachable addresses are in env as well
        else let env' = c' : env in
          maybe (return env') ((\(Closure _ e) -> addEnvironment env' e)) =<< readIORef c'

    addEnvironment :: (Traversable t, CanTrim term t)
                   => HeapRefs term t -> REnvironment IORef term t -> IO (HeapRefs term t)
    addEnvironment env e = foldr addClosure (return env) e

    addStack :: (Traversable t, CanTrim term t)
             => HeapRefs term t -> RStack IORef term t -> IO (HeapRefs term t)
    addStack env s = foldr (\case { H x -> addClosure x ; P x -> addClosure x }) (return env) s

parseNat :: Parsec Text () Integer
parseNat = do
  first <- oneOf "123456789"
  rest <- many (oneOf "0123456789")
  return (read (first : rest))

freshName :: String -> Term -> Name
freshName n t = pack (n ++ show (helper t))
  where
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


appT :: Term -> Term -> Term
appT t (Var x) = App t x
appT t t'      = let x = freshName "a" t in Let [(x , t')] (App t x)

toTerm :: LC.Term -> Term
toTerm (LC.Var n) = Var n
toTerm (LC.Lam n t) = Lam n (toTerm t)
toTerm (LC.App t t') = appT (toTerm t) (toTerm t')


withFix :: Term -> Term
withFix t = Let [ ("fix" , Lam "f" (Let [ ("fixf" , App (Var "fix") "f") ] (App (Var "f") "fixf"))) ] t



instance Show DBTerm where
  show = show . fromDBTerm

instance Show BVDBTerm where
  show = show . fromBVDBTerm

toI :: [Name] -> Name -> Int
toI [] _       = undefined
toI (n' : l) n = if n == n' then 0 else (toI l n + 1)

toDBTermCtx :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ ())
  => (XExt d1 -> XExt d2) -> [Name] -> ETerm d1 -> ETerm d2
toDBTermCtx f l (Var n)   = Var (toI l n)
toDBTermCtx f l (Lam n t) = Lam n (toDBTermCtx f (n : l) t)
toDBTermCtx f l (App t n) = App (toDBTermCtx f l t) (toI l n)
toDBTermCtx f l (Let x t) = let newCtx = map fst x ++ l
  in Let (map (\(n, t) -> (n, toDBTermCtx f newCtx t)) x) (toDBTermCtx f newCtx t)
toDBTermCtx f l (Ext x)   = Ext (f x)

toDBTerm :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ ())
  => (XExt d1 -> XExt d2) -> ETerm d1 -> ETerm d2
toDBTerm f = toDBTermCtx f []

lookupVar :: [Name] -> Int -> Name
lookupVar l i = case lookupList i l of
  (Just x) -> x
  Nothing  -> pack ("FV" ++ show (i - length l))

fromDBTermCtx :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ ())
  => (XExt d2 -> XExt d1) -> [Name] -> ETerm d2 -> ETerm d1
fromDBTermCtx _ l (Var i)   = Var (lookupVar l i)
fromDBTermCtx f l (Lam n t) = Lam n (fromDBTermCtx f (n : l) t)
fromDBTermCtx f l (App t i) = App (fromDBTermCtx f l t) (lookupVar l i)
fromDBTermCtx f l (Let x t) = let newCtx = map fst x ++ l
  in Let (map (\(n, t) -> (n, fromDBTermCtx f newCtx t)) x) (fromDBTermCtx f newCtx t)
fromDBTermCtx f _ (Ext x) = Ext (f x)

fromDBTerm :: DBTerm -> Term
fromDBTerm = fromDBTermCtx id []

fromBVDBTerm :: BVDBTerm -> BVTerm
fromBVDBTerm = fromDBTermCtx convBVCtrs' []

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

data IsLAM m e s t = IsLAM { step :: s -> m (Either e s), initS :: t -> s }

step' :: Monad m => IsLAM m e s t -> s -> m s
step' l@(IsLAM step _) s = do
  s' <- step s
  case s' of
    (Left _)    -> return s
    (Right s'') -> step' l s''

runTrace :: Monad m => IsLAM m e s t -> s -> m [s]
runTrace l@(IsLAM step _) s = do
  s' <- step s
  case s' of
    (Left _)    -> return []
    (Right s'') -> (s :) <$> runTrace l s''

runTrace' :: Monad m => IsLAM m e s t -> t -> m [s]
runTrace' l = runTrace l . initS l

evalPrint :: Show s => IsLAM IO e s t -> t -> IO ()
evalPrint l@(IsLAM _ initS) t = step' l (initS t) >>= print
