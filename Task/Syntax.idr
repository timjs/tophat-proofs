module Task.Syntax

import Helpers
import public Task.Heap
import public Task.Types

%default total

---- Labels & Names ------------------------------------------------------------

public export
Label : Type
Label = String

public export
data Name
  = Unnamed
  | Named Nat

export
Eq Name where
  (==) (Unnamed) (Unnamed)  = True
  (==) (Named k) (Named k') = k == k'
  (==) _         _          = False

export
Uninhabited (Unnamed = Named k) where
  uninhabited Refl impossible

export
namedInjective : (Named x = Named k) -> (x = k)
namedInjective Refl = Refl

public export
DecEq Name where
  decEq (Unnamed) (Unnamed)  = Yes Refl
  decEq (Named k) (Named k') with (k ?= k')
    decEq (Named k) (Named k)  | Yes Refl = Yes Refl
    decEq (Named k) (Named k') | No contra = No (contra . namedInjective)
  decEq (Unnamed) (Named k)  = No absurd
  decEq (Named k) (Unnamed)  = No (negEqSym absurd)

---- Tasks & Editors -----------------------------------------------------------

mutual

  public export
  data Task : (h : Heap) -> (a : Type) -> Type where
    ---- Editors
    Edit   : (n : Name) -> (e : Editor h a) -> Task h a
    ---- Parallels
    Pair   : (t1 : Task h a) -> (t2 : Task h b) -> Task h (a, b)
    Done   : (v : a) -> Task h a
    Choose : (t1 : Task h a) -> (t2 : Task h a) -> Task h a
    Fail   : Task h a
    ---- Steps
    Trans  : (f : a' -> a) -> (t2 : Task h a') -> Task h a
    Step   : (t1 : Task h a') -> (c : a' -> Task h a) -> Task h a
    ---- Asserts
    Assert : (p : Bool) -> Task h Bool
    Repeat : (t1 : Task h a) -> Task h a
    ---- Stores
    -- Share : {auto ok : IsBasic a} -> a -> Task h (Ref h a)
    Assign : {auto ok : IsBasic a} -> (v : a) -> (r : Ref h a) -> Task h ()

  public export
  data Editor : (h : Heap) -> (a : Type) -> Type where
    ---- Owned
    Enter  : {a : Type} -> {auto ok : IsBasic a} -> Editor h a
    Update : {a : Type} -> {auto ok : IsBasic a} -> (v : a) -> Editor h a
    View   : {a : Type} -> {auto ok : IsBasic a} -> (v : a) -> Editor h a
    Select : (ts : List (Label, Task h a)) -> Editor h a
    ---- Shared
    Change : {a : Type} -> {auto ok : IsBasic a} -> (r : Ref h a) -> Editor h a
    Watch  : {a : Type} -> {auto ok : IsBasic a} -> (r : Ref h a) -> Editor h a

public export
data IsNormal : Task h a -> Type where
  EditIsNormal   : IsNormal (Edit (Named k) e)
  PairIsNormal   : IsNormal t1 -> IsNormal t2 -> IsNormal (Pair t1 t2)
  DoneIsNormal   : IsNormal (Done v)
  ChooseIsNormal : IsNormal t1 -> IsNormal t2 -> IsNormal (Choose t1 t2)
  FailIsNormal   : IsNormal Fail
  TransIsNormal  : IsNormal t2 -> IsNormal (Trans f t2)
  StepIsNormal   : IsNormal t1 -> IsNormal (Step t1 c)

public export
NormalisedTask : Heap -> Type -> Type
NormalisedTask h a = (t : Task h a ** IsNormal t)

---- Inputs & Options ----------------------------------------------------------

---- Concrete inputs

public export
data Concrete : Type where
  Value : {a' : Type} -> {auto ok' : IsBasic a'} -> (v : a') -> Concrete

---- Symbolic inputs

public export
data Symbolic : Type where
  Symbol : (a' : Type) -> {auto ok' : IsBasic a'} -> Symbolic

public export
Eq Symbolic where
  (==) (Symbol a {ok'=ok_a}) (Symbol b {ok'=ok_b}) with (decBasic ok_a ok_b)
    (==) (Symbol a {ok'=ok_a}) (Symbol a {ok'=ok_a}) | Yes Refl = True
    (==) (Symbol a {ok'=ok_a}) (Symbol b {ok'=ok_b}) | No _ = False

symbolInjective : {auto ok_a : IsBasic a} -> {auto ok_b : IsBasic b} -> (Symbol a = Symbol b) -> (ok_a = ok_b)
symbolInjective {ok_a=ok} {ok_b=ok} Refl = Refl

public export
DecEq Symbolic where
  decEq (Symbol a {ok'=ok_a}) (Symbol b {ok'=ok_b}) with (decBasic ok_a ok_b)
    decEq (Symbol a {ok'=ok_a}) (Symbol a {ok'=ok_a}) | Yes Refl = Yes Refl
    decEq (Symbol a {ok'=ok_a}) (Symbol b {ok'=ok_b}) | No cntr = No (cntr . symbolInjective)

---- Inputs

||| Inputs are parametrised over concrete values or symbols
public export
data Input v
  = Insert Nat v
  | Option Name Label

public export
Pick : Nat -> Label -> Input v
Pick n l = Option (Named n) l

public export
Prepick : Label -> Input v
Prepick l = Option Unnamed l

-- insertInjective : (Insert k v = Insert k x) -> (v = x)
-- insertInjective Refl = Refl

-- pickInjective : (Pick n l = Pick n x) -> (l = x)
-- pickInjective Refl = Refl

public export
Eq v => Eq (Input v) where
  (==) (Insert k x) (Insert k' x') = k == k' && x == x'
  (==) (Option n l) (Option n' l') = n == n' && l == l'
  (==) _            _              = False

public export
DecEq v => DecEq (Input v) where
  decEq (Insert k x) (Insert k' x') = ?input_decEq_insert
  decEq (Option n l) (Option n' l') = ?input_decEq_pick
  decEq _            _              = ?action_decEq_rest

public export
dummify : Input Concrete -> Input Symbolic
dummify (Insert k (Value {a'} _)) = Insert k (Symbol a')
dummify (Option n l)              = Option n l
