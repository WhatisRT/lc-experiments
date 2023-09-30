{-# LANGUAGE MultiWayIf, OverloadedStrings #-}
module LAM.Test where

import Data.Text (pack)
import Test.QuickCheck

import LAM.Base
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
  shrink = filter isClosed . genericShrink

roundtrip f g t = t == f (g t)

roundtripToDB :: Term -> Bool
roundtripToDB = roundtrip fromDBTerm toDBTerm

roundtripToDBT0 :: Term -> Bool
roundtripToDBT0 = roundtrip termFromDBTTerm0 termToDBTTerm0

roundtripToDBT1 :: Term -> Bool
roundtripToDBT1 = roundtrip termFromDBTTerm1 termToDBTTerm1
