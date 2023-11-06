{-# LANGUAGE UndecidableInstances #-}

-- | Generic term type and functions.
module LAM.Types.Generic
  ( Name, XVar, XLet, XExt, ETerm(..), pattern Let, showTermWithCtx
  , fromDBTermCtx, fromDBTerm, toDBTermCtx, toDBTerm) where

import Control.Monad
import Data.IORef
import Data.List
import Data.Text (Text, pack, unpack)
import Data.Void
import GHC.Generics
import Text.Parsec hiding (State)
import Trie.Map (Trie)
import qualified Trie.Map as Trie
import Util

-- | Variable names.
type Name = Text

-- | Type family for variable names.
type family XVar a
-- | Type family for extra information at let bindings (usually trimmers).
type family XLet a
-- | Type family for extra constructors (like base values).
type family XExt a

-- | Generic term datatype.
data ETerm d
  = Var (XVar d)
  | Lam Name (ETerm d)
  | App (ETerm d) (XVar d)
  | XLet (XLet d) [(Name, ETerm d)] (ETerm d)
  | Ext !(XExt d) -- strictness makes the pattern complete when this is empty
  deriving Generic

-- | Without extra data on XLet, we can have a simplified pattern.
pattern Let :: (XLet d ~ ()) => [(Name, ETerm d)] -> ETerm d -> ETerm d
pattern Let x t = XLet () x t

{-# COMPLETE Var, Lam, App, Let, Ext #-}

deriving instance (Eq (XVar a), Eq (XLet a), Eq (XExt a)) => Eq (ETerm a)
deriving instance (Ord (XVar a), Ord (XLet a), Ord (XExt a)) => Ord (ETerm a)

-- | Show a term, with a special function to show free variables.

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

toI :: [Name] -> Name -> Int
toI [] _       = undefined
toI (n' : l) n = if n == n' then 0 else (toI l n + 1)

-- | Convert from named to DeBruijn representation in a context.
toDBTermCtx :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ ())
  => (XExt d1 -> XExt d2) -> [Name] -> ETerm d1 -> ETerm d2
toDBTermCtx f l (Var n)   = Var (toI l n)
toDBTermCtx f l (Lam n t) = Lam n (toDBTermCtx f (n : l) t)
toDBTermCtx f l (App t n) = App (toDBTermCtx f l t) (toI l n)
toDBTermCtx f l (Let x t) = let newCtx = map fst x ++ l
  in Let (map (\(n, t) -> (n, toDBTermCtx f newCtx t)) x) (toDBTermCtx f newCtx t)
toDBTermCtx f l (Ext x)   = Ext (f x)

-- | Convert from named to DeBruijn representation.
toDBTerm :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ ())
  => (XExt d1 -> XExt d2) -> ETerm d1 -> ETerm d2
toDBTerm f = toDBTermCtx f []

lookupVar :: [Name] -> Int -> Name
lookupVar l i = case lookupList i l of
  (Just x) -> x
  Nothing  -> pack ("FV" ++ show (i - length l))

-- | Convert from DeBruijn to named representation in a context.
fromDBTermCtx :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ ())
  => (XExt d2 -> XExt d1) -> [Name] -> ETerm d2 -> ETerm d1
fromDBTermCtx _ l (Var i)   = Var (lookupVar l i)
fromDBTermCtx f l (Lam n t) = Lam n (fromDBTermCtx f (n : l) t)
fromDBTermCtx f l (App t i) = App (fromDBTermCtx f l t) (lookupVar l i)
fromDBTermCtx f l (Let x t) = let newCtx = map fst x ++ l
  in Let (map (\(n, t) -> (n, fromDBTermCtx f newCtx t)) x) (fromDBTermCtx f newCtx t)
fromDBTermCtx f _ (Ext x) = Ext (f x)

-- | Convert from DeBruijn to named representation.
fromDBTerm :: (XVar d1 ~ Name, XVar d2 ~ Int, XLet d2 ~ (), XLet d1 ~ (), XExt d1 ~ XExt d2)
  => ETerm d2 -> ETerm d1
fromDBTerm = fromDBTermCtx id []
