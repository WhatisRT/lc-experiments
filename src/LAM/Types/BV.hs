-- | Terms with base values and operations, currently integers, plus and print.
module LAM.Types.BV where

import Data.Text
import LAM.Types.Generic

-- | Boxed 'Int', plus, print
data BVCtrs = CstB Int | OpPB BVTerm BVTerm | OPrB BVTerm

-- | Pattern for boxed integers
pattern Cst :: (XExt d ~ BVCtrs) => Int -> ETerm d
pattern Cst x = Ext (CstB x)

-- | Pattern for t + t'
pattern OpP :: (XExt d ~ BVCtrs) => BVTerm -> BVTerm -> ETerm d
pattern OpP t t' = Ext (OpPB t t')

-- | Pattern for print t
pattern OPr :: (XExt d ~ BVCtrs) => BVTerm -> ETerm d
pattern OPr t = Ext (OPrB t)

-- | DeBruijn version of 'BVCtrs'. Need 'RetDBBV' and 'CseDBBV' for
-- execution.
data BVDBCtrs = CstDBBV Int | RetDBBV | OpPDBBV | OPrDBBV
  | CseDBBV BVDBTerm BVDBTerm -- case e of e', single constructor

-- | Boxed 'Int'
pattern CstDB :: (XExt d ~ BVDBCtrs) => Int -> ETerm d
pattern CstDB x = Ext (CstDBBV x)

-- | Closure containing a boxed value
pattern RetDB :: (XExt d ~ BVDBCtrs) => ETerm d
pattern RetDB = Ext RetDBBV

-- | Plus, adds the two values on the top of the stack
pattern OpPDB :: (XExt d ~ BVDBCtrs) => ETerm d
pattern OpPDB = Ext OpPDBBV

-- | Print, prints the value on the top of the stack
pattern OPrDB :: (XExt d ~ BVDBCtrs) => ETerm d
pattern OPrDB = Ext OPrDBBV

-- | Case, for casing on a boxed value to access its contents
pattern CseDB :: (XExt d ~ BVDBCtrs) => BVDBTerm -> BVDBTerm -> ETerm d
pattern CseDB t t' = Ext (CseDBBV t t')

-- | Convert to DeBruijn
convBVCtrs :: BVCtrs -> BVDBCtrs
convBVCtrs (CstB x)    = CstDBBV x
convBVCtrs (OpPB t t') = CseDBBV (toDB t) (Ext (CseDBBV (toDB t') OpPDB))
  where toDB = toDBTerm convBVCtrs
convBVCtrs (OPrB t)    = CseDBBV (toDB t) OPrDB
  where toDB = toDBTerm convBVCtrs

-- | Convert to named (incomplete)
convBVCtrs' :: BVDBCtrs -> BVCtrs
convBVCtrs' (CstDBBV x) = CstB x
convBVCtrs' _ = undefined

-- | Test term
bvTest :: BVTerm
bvTest = OPr (OpP (Cst 1) (Cst 2))

-- | Phantom for named terms with base values.
data BV
type instance XVar BV = Name
type instance XLet BV = ()
type instance XExt BV = BVCtrs

-- | Phantom for DeBruijn terms with base values.
data BVDB
type instance XVar BVDB = Int
type instance XLet BVDB = ()
type instance XExt BVDB = BVDBCtrs

-- | Named terms with base values.
type BVTerm = ETerm BV
-- | DeBruijn terms with base values.
type BVDBTerm = ETerm BVDB

instance Show BVCtrs where
  show (CstB x)    = show x
  show (OpPB t t') = show t ++ " + " ++ show t'
  show (OPrB t)    = "print " ++ show t

instance Show BVTerm where
  show = showTermWithCtx show unpack

instance Show BVDBTerm where
  show = show . fromBVDBTerm

-- | DeBruijn to named
fromBVDBTerm :: BVDBTerm -> BVTerm
fromBVDBTerm = fromDBTermCtx convBVCtrs' []
