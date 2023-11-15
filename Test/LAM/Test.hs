module LAM.Test where

import Data.Text (pack)
import Test.QuickCheck

import LAM.Base
import LAM.Types.Generic
import LAM.Trim

instance Arbitrary Name where
  arbitrary = (pack . pure) <$> elements ['a'..'z']


instance Arbitrary Term where
  arbitrary = go [] 0
    where
      go :: [Name] -> Int -> Gen Term
      go c s = do
        s' <- getSize
        let varDep = [ Var <$> elements c
                     , App <$> go c s <*> elements c ]
            intro  = [ arbitrary >>= \n -> Lam n <$> go (n:c) s
                     , do
                         x <- listOf1 arbitrary
                         let genTerm = scale (`div` length x) $ go (x++c) (length x)
                         x' <- traverse (\n -> (n,) <$> genTerm) x
                         Let x' <$> genTerm
                     ]
          in oneof (if | null c -> intro
                       | length c > s' -> varDep
                       | otherwise -> intro ++ varDep)
  -- FIXME: doesn't work because of missing Arbitrary Void
  --shrink = filter isClosed . genericShrink

instance Arbitrary DBTerm where
  arbitrary = (toDBTerm id) <$> (arbitrary :: Gen Term)

roundtrip f g t = t == f (g t)

roundtripToDB :: Term -> Bool
roundtripToDB = roundtrip (fromDBTerm :: DBTerm -> Term) (toDBTerm id)

roundtripToDBT0 :: Term -> Bool
roundtripToDBT0 = roundtrip termFromDBTTerm0 termToDBTTerm0

roundtripToDBT1 :: Term -> Bool
roundtripToDBT1 = roundtrip termFromDBTTerm1 termToDBTTerm1

freeIxsProp1 :: Term -> Bool
freeIxsProp1 t = length ( freeIxs (toDBTerm id t) ) == length ( freeVars t)

freeIxsProp2 :: [Name] -> DBTerm -> Bool
freeIxsProp2 ctx t | (ctx == [] && freeIxs t == [] ) ||
                     (freeIxs t /= [] && length ctx == maximum (freeIxs t) + 1 )
                               = freeVars (fromDBTermCtx id ctx t) == ctx 
                   | otherwise = True

freeIxsProp3 :: DBTerm -> Bool
freeIxsProp3 t = all (\ x -> x >= 0) (freeIxs t)

freeVarsProp :: Name -> Term -> Bool
freeVarsProp x t = freeVars (Lam x t) == filter (\ y -> y /= x) (freeVars t)

mapFreeProp :: (Int -> Int) -> DBTerm -> Bool
mapFreeProp f t = map f (freeIxs t) == freeIxs (mapFree f t)
