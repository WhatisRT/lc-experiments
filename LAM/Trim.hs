module LAM.Trim where

-- Terms with trimmers

import Data.List
import LAM.Base

type DBTrim a = ([Int], a)

-- 0: Reindex, currenty broken

data DBTTerm0
  = DBTVar Int
  | DBTLam Name DBTTerm0
  | DBTApp DBTTerm0 Int
  | DBTLet [(Name, DBTrim DBTTerm0)] (DBTrim DBTTerm0)
--  deriving Show

instance Show DBTTerm0 where
  show = show . fromDBTTerm0

annotate :: DBTerm -> DBTrim DBTTerm0
annotate t = (ixs, toDBTTerm0 t')
  where
    ixs = freeIxs t

    t' :: DBTerm
    t' = helper 0 t

    substI :: Int -> Int -> Int
    substI k i = if i < k then i else
      case findIndex (== i-k) ixs of
        (Just x) -> x + k
        Nothing  -> error ("error: substI " ++ show k ++ " " ++ show i ++ " " ++ show ixs)

    helper :: Int -> DBTerm -> DBTerm
    helper k (DBVar i)   = DBVar $ substI k i
    helper k (DBLam n t) = DBLam n (helper (k+1) t)
    helper k (DBApp t i) = DBApp (helper k t) (substI k i)
    helper k (DBLet x t) = DBLet (map (\(n, t) -> (n, helper (k+length x) t)) x) (helper (k+length x) t)

toDBTTerm0 :: DBTerm -> DBTTerm0
toDBTTerm0 (DBVar i)   = DBTVar i
toDBTTerm0 (DBLam n t) = DBTLam n (toDBTTerm0 t)
toDBTTerm0 (DBApp t n) = DBTApp (toDBTTerm0 t) n
toDBTTerm0 (DBLet x t) = DBTLet (map (\(n, t) -> (n, annotate t)) x) (annotate t)

fromDBTTerm0Trim :: DBTrim DBTTerm0 -> DBTerm
fromDBTTerm0Trim (e, t) = go 0 t
  where
    substI :: Int -> Int -> Int
    substI k i = if i < k then i
      else if i-k < length e then (e !! (i-k)) + k
      else i -- error ("substI (" ++ show e ++ ", " ++ show t ++ ") " ++ show k ++ " " ++ show i)

    helper :: Int -> DBTrim DBTTerm0 -> DBTerm
    helper k (e', t) = fromDBTTerm0Trim (map (substI k) e', t)

    go k (DBTVar i)   = DBVar (substI k i)
    go k (DBTLam n t) = DBLam n (go (k+1) t)
    go k (DBTApp t i) = DBApp (go k t) (substI k i)
    go k (DBTLet x t) = DBLet (map (\(n, t) -> (n, helper (k+length x) t)) x) (helper (k+length x) t)

fromDBTTerm0 :: DBTTerm0 -> DBTerm
fromDBTTerm0 t = fromDBTTerm0Trim ([], t)


toDBTTerm0' :: Term -> DBTTerm0
toDBTTerm0' = toDBTTerm0 . toDBTerm

termFromDBTTerm0 :: DBTTerm0 -> Term
termFromDBTTerm0 = fromDBTerm . fromDBTTerm0

termToDBTTerm0 :: Term -> DBTTerm0
termToDBTTerm0 = toDBTTerm0 . toDBTerm

-- just add trimmers, slow lookup

data DBTTerm1
  = DBTVar1 Int
  | DBTLam1 Name DBTTerm1
  | DBTApp1 DBTTerm1 Int
  | DBTLet1 [(Name, DBTrim DBTTerm1)] (DBTrim DBTTerm1)

instance Show DBTTerm1 where
  show = show . fromDBTTerm1

annotate1 :: DBTerm -> DBTrim DBTTerm1
annotate1 t = (freeIxs t, toDBTTerm1 t)

toDBTTerm1 :: DBTerm -> DBTTerm1
toDBTTerm1 (DBVar i)   = DBTVar1 i
toDBTTerm1 (DBLam n t) = DBTLam1 n (toDBTTerm1 t)
toDBTTerm1 (DBApp t n) = DBTApp1 (toDBTTerm1 t) n
toDBTTerm1 (DBLet x t) = DBTLet1 (map (\(n, t) -> (n, annotate1 t)) x) (annotate1 t)

fromDBTTerm1 :: DBTTerm1 -> DBTerm
fromDBTTerm1 (DBTVar1 i)   = DBVar i
fromDBTTerm1 (DBTLam1 n t) = DBLam n (fromDBTTerm1 t)
fromDBTTerm1 (DBTApp1 t i) = DBApp (fromDBTTerm1 t) i
fromDBTTerm1 (DBTLet1 x t) = DBLet (map (\(n, t) -> (n, fromDBTTerm1 $ snd t)) x) (fromDBTTerm1 $ snd t)

trimLookup1 :: [Int] -> Int -> Maybe Int
trimLookup1 l i = findIndex (==i) l

termFromDBTTerm1 :: DBTTerm1 -> Term
termFromDBTTerm1 = fromDBTerm . fromDBTTerm1

termToDBTTerm1 :: Term -> DBTTerm1
termToDBTTerm1 = toDBTTerm1 . toDBTerm
