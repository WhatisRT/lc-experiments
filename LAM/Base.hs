{-# LANGUAGE LambdaCase, OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes, FunctionalDependencies #-}
module LAM.Base where

import Text.Parsec
import Data.Text (Text, pack, unpack)
import Data.List
import Data.Maybe
import Trie.Map (Trie)
import qualified Data.Map as Map

import GHC.Generics
import Data.List
import Data.IORef

import qualified LC.Base as LC

type Name = Text

data Term
  = Var Name
  | Lam Name Term
  | App Term Name
  | Let [(Name, Term)] Term
  deriving (Eq, Ord, Generic)

freeVars :: Term -> [Name]
freeVars = nub . go []
  where
    addVar ctx x = if x `elem` ctx then [] else [x]

    go ctx (Var x)   = addVar ctx x
    go ctx (Lam x t) = go (x:ctx) t
    go ctx (App t x) = go ctx t ++ addVar ctx x
    go ctx (Let x t) = let ctx' = map fst x ++ ctx in
      concatMap (go ctx') (map snd x) ++ go ctx' t

isClosed :: Term -> Bool
isClosed = null . freeVars

-- special function to show free variables
showTermWithCtx :: (Name -> String) -> Term -> String
showTermWithCtx showFree = go []
  where
    showVar ctx x = if x `elem` ctx then unpack x else showFree x

    go :: [Name] -> Term -> String
    go ctx (Var x)   = showVar ctx x
    go ctx (Lam x t) = "λ " ++ unpack x ++ ". " ++ go (x:ctx) t
    go ctx (App t x) = "(" ++ go ctx t ++ " " ++ showVar ctx x ++ ")"
    go ctx (Let x t) = let ctx' = map fst x ++ ctx in
      "let " ++ concat (intersperse "; " (map (\(n, t) -> unpack n ++ " = " ++ go ctx' t) x))
      ++ " in " ++ go ctx' t

instance Show Term where
  show = showTermWithCtx unpack

newtype NamedList a = NamedList [(Name, a)]
  deriving (Functor, Foldable, Traversable, Show)

type Control = Term

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
      (Left e)  -> Nothing
      (Right i) -> Just i

    toNsuc :: Name -> Integer
    toNsuc n' = case parseN n' of
      (Just x) -> succ x
      Nothing  -> 0

    helper :: Term -> Integer
    helper (Var x)   = toNsuc x
    helper (Lam x t) = helper t
    helper (App t x) = max (helper t) (toNsuc x)
    helper (Let x t) = foldl max (helper t) (map (helper . snd) x)


appT :: Term -> Term -> Term
appT t (Var x) = App t x
appT t t'      = let x = freshName "a" t in Let [(x , t')] (App t x)

toTerm :: LC.Term -> Term
toTerm (LC.Var n) = Var n
toTerm (LC.Lam n t) = Lam n (toTerm t)
toTerm (LC.App t t') = appT (toTerm t) (toTerm t')

data Tag a = P a
           | H a deriving (Eq, Show, Functor, Foldable, Traversable)


withFix :: Term -> Term
withFix t = Let [ ("fix" , Lam "f" (Let [ ("fixf" , App (Var "fix") "f") ] (App (Var "f") "fixf"))) ] t



data DBTerm
  = DBVar Int
  | DBLam Name DBTerm
  | DBApp DBTerm Int
  | DBLet [(Name, DBTerm)] DBTerm

instance Show DBTerm where
  show = show . fromDBTerm

lookupList :: (Eq a) => Int -> [a] -> Maybe a
lookupList x [] = Nothing
lookupList x (a : as) = if x == 0 then Just a else lookupList (x-1) as

lookup' :: (Eq a, Show a) => Int -> [a] -> a
lookup' i l = case lookupList i l of
  (Just x) -> x
  Nothing  -> error ("lookup': " ++ show i ++ " " ++ show l)

toDBTerm :: Term -> DBTerm
toDBTerm = helper []
  where
    toI :: [Name] -> Name -> Int
    toI [] n       = undefined
    toI (n' : l) n = if n == n' then 0 else (toI l n + 1)

    helper :: [Name] -> Term -> DBTerm
    helper l (Var n)   = DBVar (toI l n)
    helper l (Lam n t) = DBLam n (helper (n : l) t)
    helper l (App t n) = DBApp (helper l t) (toI l n)
    helper l (Let x t) = let newCtx = map fst x ++ l
      in DBLet (map (\(n, t) -> (n, helper newCtx t)) x) (helper newCtx t)

lookupVar :: [Name] -> Int -> Name
lookupVar l i = case lookupList i l of
  (Just x) -> x
  Nothing  -> pack ("FV" ++ show (i - length l))

fromDBTermCtx :: [Name] -> DBTerm -> Term
fromDBTermCtx l (DBVar i)   = Var (lookupVar l i)
fromDBTermCtx l (DBLam n t) = Lam n (fromDBTermCtx (n : l) t)
fromDBTermCtx l (DBApp t i) = App (fromDBTermCtx l t) (lookupVar l i)
fromDBTermCtx l (DBLet x t) = let newCtx = map fst x ++ l
  in Let (map (\(n, t) -> (n, fromDBTermCtx newCtx t)) x) (fromDBTermCtx newCtx t)

fromDBTerm :: DBTerm -> Term
fromDBTerm = fromDBTermCtx []

freeIxs :: DBTerm -> [Int]
freeIxs = nub . sort . helper
  where
    strengthenBy :: Int -> [Int] -> [Int]
    strengthenBy n l = map (\k -> k-n) (filter (\x -> not (elem x [0..n-1])) l)

    helper :: DBTerm -> [Int]
    helper (DBVar i)   = [i]
    helper (DBLam _ t) = strengthenBy 1 (helper t)
    helper (DBApp t i) = i : helper t
    helper (DBLet x t) = strengthenBy (length x) (concatMap (\(_,t) -> helper t) x ++ helper t)

mapFree :: (Int -> Int) -> DBTerm -> DBTerm
mapFree f = go 0
  where
    modI ctx i = if i < ctx then i else (f (i - ctx)) + ctx

    go :: Int -> DBTerm -> DBTerm
    go ctx (DBVar i)   = DBVar (modI ctx i)
    go ctx (DBLam n t) = DBLam n (go (ctx+1) t)
    go ctx (DBApp t i) = DBApp (go ctx t) (modI ctx i)
    go ctx (DBLet x t) = let ctx' = ctx+length x in
      DBLet (map (\(n, t') -> (n, go ctx' t')) x) (go ctx' t)

data IsLAM m e s t = IsLAM { step :: s -> m (Either e s), initS :: t -> s }

step' :: Monad m => IsLAM m e s t -> s -> m s
step' l@(IsLAM step initS) s = do
  s' <- step s
  case s' of
    (Left _)    -> return s
    (Right s'') -> step' l s''

runTrace :: Monad m => IsLAM m e s t -> s -> m [s]
runTrace l@(IsLAM step initS) s = do
  s' <- step s
  case s' of
    (Left _)    -> return []
    (Right s'') -> (s :) <$> runTrace l s''

runTrace' :: Monad m => IsLAM m e s t -> t -> m [s]
runTrace' l = runTrace l . initS l

evalPrint :: Show s => IsLAM IO e s t -> t -> IO ()
evalPrint l@(IsLAM step initS) t = do
  s <- step' l (initS t)
  putStrLn (show s)
