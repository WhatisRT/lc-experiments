{-# OPTIONS --guardedness #-}

module IORef where

import IO.Primitive as Prim
open import Data.Unit
open import IO using (IO; run; readFiniteFile; lift)

{-#
  FOREIGN GHC
  import Data.IORef
#-}

private variable
  A : Set

postulate
  IORef : Set → Set

  newIORefPrim    : A -> Prim.IO (IORef A)
  readIORefPrim   : IORef A -> Prim.IO A
  writeIORefPrim  : IORef A -> A -> Prim.IO ⊤
  modifyIORefPrim : IORef A -> (A -> A) -> Prim.IO ⊤
  modifyIORef'Prim : IORef A -> (A -> A) -> Prim.IO ⊤

{-# COMPILE GHC IORef = type IORef #-}
{-# COMPILE GHC newIORefPrim = \_ -> newIORef #-}
{-# COMPILE GHC readIORefPrim = \_ -> readIORef #-}
{-# COMPILE GHC writeIORefPrim = \_ -> writeIORef #-}
{-# COMPILE GHC modifyIORefPrim = \_ -> modifyIORef #-}
{-# COMPILE GHC modifyIORef'Prim = \_ -> modifyIORef' #-}

newIORef : A -> IO (IORef A)
newIORef a = lift (newIORefPrim a)

readIORef : IORef A -> IO A
readIORef r = lift (readIORefPrim r)

writeIORef : IORef A -> A -> IO ⊤
writeIORef r a = lift (writeIORefPrim r a)

modifyIORef : IORef A -> (A -> A) -> IO ⊤
modifyIORef r f = lift (modifyIORefPrim r f)

modifyIORef' : IORef A -> (A -> A) -> IO ⊤
modifyIORef' r f = lift (modifyIORef'Prim r f)
