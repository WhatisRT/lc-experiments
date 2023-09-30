{-# OPTIONS --sized-types --guardedness #-}
module LAM2 where

open import Utils
open import Utils.Trie
open import Pretty
import LC

open import Function
open import Data.Nat
open import Data.List hiding (lookup; intersperse) renaming (_++_ to _++L_)
open import Data.Product hiding (map; zip)
open import Data.String using (String; toList; fromList; _<+>_; _++_; intersperse)
open import Data.Bool
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; maybe; maybe′)
open import Data.Unit.Polymorphic
import Data.Unit as U

import Data.Char.Properties as C
import Data.Trie C.<-strictTotalOrder as T

open import IO
import IO.Primitive as Prim
open import IORef
open import Addr

import Containers as C

open import Foreign.Haskell
open import Foreign.Haskell.Coerce

open IO.List

open import LAM.Base

private variable A B : Set

{-# FOREIGN GHC
  import MAlonzo.Code.LAM.Base
  import Text.Pretty.Simple
  import Text.Pretty.Simple.Internal.Color
#-}

TA : Set → Set
TA A = C.CSet × A

freeVarsS : Term → C.CSet
freeVarsS t = C.setFromList (freeVars t)

-- trimmer-annotated terms
data TATerm : Set where
  Var : Name → TATerm
  Lam : Name → TATerm → TATerm
  App : TATerm → Name → TATerm
  Let : List (TA Name × TATerm) → TA TATerm → TATerm

{-# TERMINATING #-}
annotate : Term → TATerm
annotate (Var x) = Var x
annotate (Lam x t) = Lam x (annotate t)
annotate (App t x) = App (annotate t) x
annotate (Let x t) = Let (map (λ (n , t) → (freeVarsS t , n) , annotate t) x) (freeVarsS t , annotate t)

{-# TERMINATING #-}
dropAnn : TATerm → Term
dropAnn (Var x) = Var x
dropAnn (Lam x t) = Lam x (dropAnn t)
dropAnn (App t x) = App (dropAnn t) x
dropAnn (Let x (_ , t)) = Let (map (λ ((_ , n) , t) → n , dropAnn t) x) (dropAnn t)

instance
  Show-TATerm : Show TATerm
  Show-TATerm .show = show ∘ dropAnn

Map : Set → Set
Map = C.Map

{-# NO_POSITIVITY_CHECK #-}
record Closure : Set where
  inductive
  pattern
  constructor ⟨_,_⟩
  field t : TATerm
        e : Map (IORef (Maybe Closure))

HeapPointer Environment : Set

HeapPointer = IORef (Maybe Closure)
Environment = Map HeapPointer

trimEnv : C.CSet → Environment → Environment
trimEnv S E = C.restrictKeys E S

Heap Control Stack State Err : Set

Heap = Trie Closure

Control = TATerm

data Tag (A : Set) : Set where
  %_ #_ : A → Tag A

{-# COMPILE GHC Tag = data Tag (P | H) #-}

instance
  Show-Tag : ⦃ _ : Show A ⦄ → Show (Tag A)
  Show-Tag .show (% x) = "%" ++ show x
  Show-Tag .show (# x) = "#" ++ show x

mapTag : (A → B) → Tag A → Tag B
mapTag f (% x) = % (f x)
mapTag f (# x) = # (f x)

Stack = List (Tag HeapPointer)

Err = String

State = Control × Environment × Stack

--------------------------------------------------------------------------------
-- Printing
--------------------------------------------------------------------------------

PClosure PHeap PEnvironment PHeapPointer : Set
PHeapPointer = ℕ

PClosure = Term × PEnvironment
PHeap = List (PHeapPointer × Maybe PClosure)
PEnvironment = List (Name × PHeapPointer)
PStack = List (Tag PHeapPointer)

FPClosure FPHeap FPEnvironment : Set

FPClosure = Pair Foreign.Term FPEnvironment
FPHeap = List (Pair PHeapPointer (Maybe FPClosure))
FPEnvironment = List (Pair Name PHeapPointer)

record FPState : Set where
  field heap : FPHeap
        closure : FPClosure
        stack : PStack

{-# COMPILE GHC FPState = data State (State) #-}

record PState : Set where
  constructor ⟨_,_,_⟩ˢ
  field heap : PHeap
        closure : PClosure
        stack : PStack

instance
  Coercible-PState : Coercible PState FPState
  Coercible-PState = TrustMe

postulate
  pPrint' : FPState → Prim.IO U.⊤

{-# COMPILE GHC pPrint' = pPrintOpt NoCheckColorTty opts #-}

pPrint = lift ∘ pPrint' ∘ coerce

ioRefAddr : IORef A → IO ℕ
ioRefAddr r = unsafeAddr <$> readIORef r

showTag : (Tag HeapPointer) → IO String
showTag (% x) = do a ← ioRefAddr x; pure ("%" ++ show a)
showTag (# x) = do a ← ioRefAddr x; pure ("#" ++ show a)

showIORefAddr : IORef A → IO String
showIORefAddr r = do a ← ioRefAddr r; pure (show a)

toPEnv : Environment → IO PEnvironment
toPEnv E = forM (C.mapToList E) λ (n , r) → (n ,_) <$> (ioRefAddr r)

toPClosure : Closure → IO PClosure
toPClosure ⟨ t , E ⟩ = (dropAnn t ,_) <$> toPEnv E

{-# TERMINATING #-}
getHeap : Environment → IO PHeap
getHeap = addEnvironment []
  where
    addClosure : PHeap → IORef (Maybe Closure) → IO PHeap
    addEnvironment : PHeap → Environment → IO PHeap

    addClosure Γ r = do
      a ← ioRefAddr r
      if a ∈ᵇ map proj₁ Γ
        then pure Γ -- if an address is in Γ, all transitively reachable addresses are in Γ as well
        else do
          c ← readIORef r
          c' ← maybe (λ c → just <$> toPClosure c) (pure nothing) c
          maybe (λ where ⟨ _ , E ⟩ → addEnvironment ((a , c') ∷ Γ) E) (pure ((a , c') ∷ Γ)) c

    addEnvironment Γ E = foldl (λ Γ' r → (λ Γ → addClosure Γ r) =<< Γ') (pure Γ) (map proj₂ $ C.mapToList E)

toPStack : Stack → IO PStack
toPStack = mapM (λ where (% x) → %_ <$> ioRefAddr x ; (# x) → #_ <$> ioRefAddr x)

toPState : State → IO PState
toPState (t , E , S) = do
  Γ ← getHeap E
  E ← toPEnv E
  S ← toPStack S
  pure ⟨ Γ , (dropAnn t , E) , S ⟩ˢ

findIndex : ⦃ _ : EqB A ⦄ → List A → A → Maybe ℕ
findIndex [] a = nothing
findIndex (x ∷ l) a = if x == a then just 0 else Data.Maybe.map suc (findIndex l a)

simpHeapAddrs : PState → PState
simpHeapAddrs ⟨ Γ , c , S ⟩ˢ = ⟨ map (λ (p , c) → mapAddr p , Data.Maybe.map simpClosure c) Γ
                              , simpClosure c
                              , map (mapTag mapAddr) S ⟩ˢ
  where
    heapAddrs : List PHeapPointer
    heapAddrs = map proj₁ Γ

    mapAddr : PHeapPointer → PHeapPointer
    mapAddr = maybe id 9999 ∘ findIndex heapAddrs

    simpClosure : PClosure → PClosure
    simpClosure (t , E) = t , map (map₂ mapAddr) E



prettyPClosure : PClosure → String
prettyPClosure (t , E) = show t ++ "," <+> (show $ map (λ (n , p) → n <+> "↦" <+> show p) E)

prettyPState : PState → String
prettyPState ⟨ Γ , c , S ⟩ˢ = intersperse "\n"
  $ ("Heap:" <+> (pretty $ map (λ (p , c) → (p , maybe prettyPClosure "⟨Black hole⟩" c)) Γ))
  ∷ ("Control:" <+> prettyPClosure c)
  ∷ ("Stack:" <+> show S)
  ∷ []

prettyPState' : PState → String
prettyPState' = prettyPState ∘ simpHeapAddrs

{-# TERMINATING #-}
convClosure : Closure → IO Term
convClosure ⟨ Var x , E ⟩ = case C.lookup x E of λ where
  nothing → pure (Var x)
  (just p) → do
    (just c) ← readIORef p
      where nothing → pure (Var x)
    convClosure c
convClosure ⟨ Lam x t , E ⟩ = do t ← convClosure ⟨ t , E ⟩; pure (Lam x t)
convClosure ⟨ App t x , E ⟩ = do
  t ← convClosure ⟨ t , E ⟩
  t' ← convClosure ⟨ Var x , E ⟩
  pure (AppT t t')
convClosure ⟨ Let x (_ , t) , E ⟩ = do
  t ← convClosure ⟨ t , E ⟩
  x ← mapM (λ where (n , t) → do t ← convClosure ⟨ t , E ⟩; pure (proj₂ n , t)) x
  pure (Let x t)

showStack : Stack → IO String
showStack S = show <$> forM S showTag

{-# TERMINATING #-}
showClosure : ℕ → List ℕ → Closure → IO String
showClosure indent l ⟨ t , E ⟩ = do
  cs ← flip mapM (C.mapToList E) (λ where (n , r) → do
    a ← ioRefAddr r
    if a ∈ᵇ l
      then pure (nothing {A = String × ℕ × (Maybe Closure)})
      else do c ← readIORef r; pure (just (n , a , c)))
  let cs' = catMaybes cs
  E' ← flip mapM cs' (λ where (n , a , c) → do
    c ← maybe′ (showClosure (suc indent) (l Data.List.++ map (proj₁ ∘ proj₂) cs')) (pure "⟨Black hole⟩") c
    pure (n <+> "↦" <+> "#" ++ show a <+> "←" <+> c))
  pure ("⟨" ++ show t ++ "," <+> show E' ++ "⟩")

showState : State → IO String
showState (t , E , S) = do
  t ← showClosure 0 [] ⟨ t , E ⟩
  S ← showStack S
  pure (t ++ "\nStack:" <+> S ++ "\n")

prettyState : State → IO String
prettyState (t , E , S) = do t ← convClosure ⟨ t , E ⟩; pure (show t)

prettyState' : State → IO ⊤
prettyState' S = (toPState S >>= (pPrint ∘ coerce ∘ simpHeapAddrs)) >> putStrLn ""

printState : State → IO ⊤
printState s = prettyState' s

--------------------------------------------------------------------------------
-- Abstract machine
--------------------------------------------------------------------------------

mark2 : State → IO (State ⊎ Err)
mark2 (Var x , E , S) = case C.lookup x E of λ where
  nothing  → pure (inj₂ "Bug: Var: lookup failed")
  (just p) → do
    just ⟨ e' , E' ⟩ ← readIORef p
      where nothing → pure (inj₂ "Var: black hole")
    writeIORef p nothing -- insert black hole
    pure (inj₁ (e' , E' , # p ∷ S))
mark2 (Lam y e     , E , [])        = pure (inj₂ "Finished: Lam: stack empty")
mark2 (Lam y e     , E , (% p) ∷ S) = pure (inj₁ (e , C.insert y p E , S))
mark2 (t@(Lam _ _) , E , (# p) ∷ S) = do
  writeIORef p (just ⟨ t , E ⟩)
  pure (inj₁ (t , E , S))
mark2 (App e x     , E , S) = case C.lookup x E of λ where
  nothing  → pure (inj₂ "Bug: App: lookup failed")
  (just p) → pure (inj₁ (e , E , % p ∷ S))
mark2 (t@(Let x e) , E , S) = do
  ext ← mapM (λ where (n , t) → do r ← newIORef nothing ; pure (n ,′ r ,′ t)) x
  let E' = C.insertMulti (map (λ where (n , r , t) → (proj₂ n , r)) ext) E
  mapM (λ where (n , r , t) → writeIORef r (just ⟨ t , trimEnv (proj₁ n) E' ⟩)) ext
  pure (inj₁ (proj₂ e , trimEnv (proj₁ e) E' , S))

{-# TERMINATING #-}
mark2' : State → IO State
mark2' s = do
  (inj₁ s') ← mark2 s
    where (inj₂ _) → pure s
  mark2' s'

{-# TERMINATING #-}
mark2'Trace : State → IO State
mark2'Trace s = do
  printState s
  (inj₁ s') ← mark2 s
    where (inj₂ _) → pure s
  mark2'Trace s'

initS : Term → State
initS t = (annotate t , C.mapFromList [] , [])

-- evalN : ℕ → Term → State ⊎ Err
-- evalN zero t    = inj₁ $ initS t
-- evalN (suc n) t = case evalN n t of λ where
--   (inj₁ x) → mark2 x
--   (inj₂ y) → inj₂ ("Error at step" <+> show n ++ ":" <+> y)

-- eval : Term → IO (Term ⊎ Err)
-- eval t = do
--   (t@(Lam _ _) , _ , []) ← mark2' (initS t)
--     where _ → pure (inj₂ "Black hole")
--   pure (inj₁ t)

evalPrint : Term → IO U.⊤
evalPrint t = do
  s ← mark2' (initS t) >>= prettyState
  IO.putStrLn s
  pure _

evalPrint' : Term → IO U.⊤
evalPrint' t = do
  mark2'Trace (initS t)
  pure _

runT : Foreign.Term → Prim.IO U.⊤
runT t = run $ evalPrint (coerce t)
{-# COMPILE GHC runT as runT #-}

runT' : Foreign.Term → Prim.IO U.⊤
runT' t = run $ evalPrint' (coerce t)
{-# COMPILE GHC runT' as runT' #-}

-- {-# TERMINATING #-}
-- mark2'Trace : State → List State
-- mark2'Trace s = case mark2 s of λ where
--   (inj₁ s') → s ∷ mark2'Trace s'
--   (inj₂ _)  → [ s ]

-- evalTrace : Term → List State
-- evalTrace t = mark2'Trace (T.empty , t , T.empty , [])


--------------------------------------------------------------------------------
-- Test terms
--------------------------------------------------------------------------------

showTerm' : Term → String
showTerm' (Var x) = "(Var" <+> show x ++ ")"
showTerm' (Lam x t) = "(Lam" <+> show x <+> {!showTerm' t!} ++ ")"
showTerm' (App t x) = {!!}
showTerm' (Let x t) = {!!}

termId  = toTerm LC.termId
term1   = toTerm LC.term1
term2   = toTerm LC.term2
term2Id = toTerm LC.term2Id
term3   = toTerm LC.term3
term5   = toTerm LC.term5
term6   = toTerm LC.term6

-- term4 = Let [ 𝕟 "x" , Var 𝕟 "x" ] (Var "x")

term7 : Term
term7 = Let [ "s" , termId ] (Let (("p" , App (Var "q") "s") ∷ [ "q" , Lam "y" (Let [ "r" , Var "y" ] (Var "r")) ]) (Var "p"))
-- let s = λ z. z in let p = (q s); q = (λ y. let r = y in r) in p

term8 : Term
term8 = Let (("y" , termId) ∷ [ "v" , App (Lam "z" (Var "z")) "y" ]) (App (Var "v") "v")


-- _ : term2Id ≡ term2 [ termId / "y" ]
-- _ = refl

bench1   = withFix $ toTerm LC.bench1
bench2   = withFix $ toTerm LC.bench2
bench3   = withFix $ toTerm LC.bench3
bench4   = withFix $ toTerm LC.bench4
t1       = withFix $ toTerm LC.test1


bench1' bench2' bench3' bench4' : Foreign.Term
bench1' = coerce bench1
{-# COMPILE GHC bench1' as bench1 #-}

bench2' = coerce bench2
{-# COMPILE GHC bench2' as bench2 #-}

bench3' = coerce bench3
{-# COMPILE GHC bench3' as bench3 #-}

bench4' = coerce bench4
{-# COMPILE GHC bench4' as bench4 #-}

test1 : Foreign.Term
test1 = coerce bench3
{-# COMPILE GHC test1 as test1 #-}

test2 : Foreign.Term
test2 = coerce t1
{-# COMPILE GHC test2 as test2 #-}

test3 : Foreign.Term
test3 = coerce term8
{-# COMPILE GHC test3 as test3 #-}
