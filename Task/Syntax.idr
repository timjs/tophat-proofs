module Task.Syntax

import Helpers
import public Task.Heap
import public Task.Reflection

%default total

---- Labels & Names ------------------------------------------------------------

export
Label : Type
Label = String

public export
data Name
  = Unnamed
  | Named Nat

export
Eq Name where
  (==) (Unnamed) (Unnamed)  = True
  (==) (Named i) (Named i') = i == i'
  (==) _         _          = False

Uninhabited (Unnamed = Named i) where
  uninhabited Refl impossible

named_inj : (Named i = Named j) -> (i = j)
named_inj Refl = Refl

public export
DecEq Name where
  decEq (Unnamed) (Unnamed)  = Yes Refl
  decEq (Named i) (Named i') with (i ?= i')
    decEq (Named i) (Named i)  | Yes Refl = Yes Refl
    decEq (Named i) (Named i') | No contra = No (contra . named_inj)
  decEq (Unnamed) (Named i)  = No absurd
  decEq (Named i) (Unnamed)  = No (negEqSym absurd)

---- Tasks & Editors -----------------------------------------------------------

mutual

  public export
  data Task : (h : Heap) -> (a : Type) -> Type where
    ---- Editors
    Edit : (n : Name) -> (e : Editor h a) -> Task h a
    ---- Parallels
    Pair : (t1 : Task h a) -> (t2 : Task h b) -> Task h (a, b)
    Done : (v : a) -> Task h a
    Choose : (t1 : Task h a) -> (t2 : Task h a) -> Task h a
    Fail : Task h a
    ---- Steps
    Trans : (f : a' -> a) -> (t : Task h a') -> Task h a
    Step : (t : Task h a') -> (c : a' -> Task h a) -> Task h a
    ---- Asserts
    Assert : (p : Bool) -> Task h Bool
    ---- Stores
    -- Share : Reflect a => a -> Task h (Ref h a)
    Assign : Reflect a => (v : a) -> (r : Ref h a) -> Task h ()

  public export
  data Editor : (h : Heap) -> (a : Type) -> Type where
    ---- Owned
    Enter : {a : Type} -> Reflect a => Editor h a
    Update : {a : Type} -> Reflect a => (v : a) -> Editor h a
    View : {a : Type} -> Reflect a => (v : a) -> Editor h a
    Select : (ts : List (Label, Task h a)) -> Editor h a
    ---- Shared
    Change : {a : Type} -> Reflect a => (r : Ref h a) -> Editor h a
    Watch : {a : Type} -> Reflect a => (r : Ref h a) -> Editor h a

---- Inputs & Options ----------------------------------------------------------

---- Concrete inputs

public export
data Concrete : Type where
  AConcrete : Reflect a => (v : a) -> Concrete

---- Symbolic inputs

public export
data Symbolic : Type where
  ASymbolic : (a : Type) -> Reflect a => Symbolic

-- public export
-- Eq Symbolic where
  -- (==) (ASymbolic a) (ASymbolic b) with (typEq a b)
  --   (==) (ASymbolic a) (ASymbolic b) | Yes Refl  = True
  --   (==) (ASymbolic a) (ASymbolic b) | No contra = False

symbolic_inj : Reflect a => Reflect x => (ASymbolic a = ASymbolic x) -> (a = x)
symbolic_inj Refl = Refl

-- public export
-- DecEq Symbolic where
  -- decEq (ASymbolic a) (ASymbolic b) with (typEq a b)
  --   decEq (ASymbolic a) (ASymbolic b) | Yes Refl = Yes Refl
  --   decEq (ASymbolic a) (ASymbolic b) | No contra = No (contra . symbolic_inj)

---- Input actions

public export
data Action k
  = AEnter k
  | ASelect Label

public export
Eq k => Eq (Action k) where
  (==) (AEnter x)  (AEnter x')  = x == x'
  (==) (ASelect l) (ASelect l') = l == l'
  (==) _           _            = False

---- Full inputs

public export
data Input k
  = AInput Name (Action k)

public export
Eq k => Eq (Input k) where
  (==) (AInput n a)  (AInput n' a')  = n == n' && a == a'
  (==) _             _               = False

public export
DecEq k => DecEq (Input k) where
  decEq (AInput n a) (AInput n' a') = ?h_1

---- Options

public export
data Option
  = AOption Name Label

export
fromOption : Option -> Input b
fromOption (AOption n l) = AInput n (ASelect l)