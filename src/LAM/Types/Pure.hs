-- | Types for pure lambda calculus with no base values. Named and DeBruijn.
module LAM.Types.Pure where

import Data.Text
import Data.Void
import LAM.Types.Generic

-- | Phantom for named terms.
data Base
type instance XVar Base = Name
type instance XLet Base = ()
type instance XExt Base = Void

-- | Phantom for DeBruijn terms.
data DB
type instance XVar DB = Int
type instance XLet DB = ()
type instance XExt DB = Void

-- | Named terms.
type Term = ETerm Base
-- | DeBruijn terms.
type DBTerm = ETerm DB

instance Show Term where
  show = showTermWithCtx absurd unpack

instance Show DBTerm where
  show t = show (fromDBTerm t :: Term)
