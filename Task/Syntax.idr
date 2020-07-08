module Task.Syntax

import Helpers
import public Task.Heap
import public Task.Types

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
    -- Share : IsBasic a => a -> Task h (Ref h a)
    Assign : IsBasic a => (v : a) -> (r : Ref h a) -> Task h ()

  public export
  data Editor : (h : Heap) -> (a : Type) -> Type where
    ---- Owned
    Enter : {a : Type} -> IsBasic a => Editor h a
    Update : {a : Type} -> IsBasic a => (v : a) -> Editor h a
    View : {a : Type} -> IsBasic a => (v : a) -> Editor h a
    Select : (ts : List (Label, Task h a)) -> Editor h a
    ---- Shared
    Change : {a : Type} -> IsBasic a => (r : Ref h a) -> Editor h a
    Watch : {a : Type} -> IsBasic a => (r : Ref h a) -> Editor h a

---- Inputs & Options ----------------------------------------------------------

---- Concrete inputs

public export
data Concrete : Type where
  AConcrete : IsBasic t => (v : t) -> Concrete

---- Symbolic inputs

public export
data Symbolic : Type where
  ASymbolic : (t : Type) -> {auto p : IsBasic t} -> Symbolic

public export
Eq Symbolic where
  (==) (ASymbolic a {p=p_a}) (ASymbolic b {p=p_b}) with (decInj p_a p_b)
    (==) (ASymbolic a {p=p_a}) (ASymbolic a {p=p_b}) | Yes Refl = True
    (==) (ASymbolic a {p=p_a}) (ASymbolic b {p=p_b}) | No _ = False

symbolicInjective : IsBasic a => IsBasic x => (ASymbolic a = ASymbolic x) -> (a = x)
symbolicInjective Refl = Refl

public export
DecEq Symbolic where
  decEq (ASymbolic a {p=p_a}) (ASymbolic b {p=p_b}) with (decInj p_a p_b)
    decEq (ASymbolic a {p=p_a}) (ASymbolic a {p=p_b}) | Yes Refl = Yes ?symbolic_decEq_yes
    decEq (ASymbolic a {p=p_a}) (ASymbolic b {p=p_b}) | No cntr = No (cntr . symbolicInjective)

---- Input actions

public export
data Action k
  = AEnter k
  | ASelect Label

enterInjective : (AEnter k = AEnter x) -> (k = x)
enterInjective Refl = Refl

selectInjective : (ASelect l = ASelect x) -> (l = x)
selectInjective Refl = Refl

public export
Eq k => Eq (Action k) where
  (==) (AEnter x)  (AEnter x')  = x == x'
  (==) (ASelect l) (ASelect l') = l == l'
  (==) _           _            = False

public export
DecEq k => DecEq (Action k) where
  decEq (AEnter x)  (AEnter x')  with (x ?= x')
    decEq (AEnter x)  (AEnter x)  | Yes Refl = Yes Refl
    decEq (AEnter x)  (AEnter x') | No cntr = No (cntr . enterInjective)
  decEq (ASelect l) (ASelect l') with (l ?= l')
    decEq (ASelect l) (ASelect l)  | Yes Refl = Yes Refl
    decEq (ASelect l) (ASelect l') | No cntr = No (cntr . selectInjective)
  decEq _           _            = ?action_decEq_rest

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
  decEq (AInput n a) (AInput n' a') with (n ?= n', a ?= a')
    decEq (AInput n a) (AInput n' a') | with_pat = ?input_decEq_rest

---- Options

public export
data Option
  = AOption Name Label

export
fromOption : Option -> Input b
fromOption (AOption n l) = AInput n (ASelect l)