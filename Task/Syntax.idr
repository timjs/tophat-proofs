module Task.Syntax

import Helpers
import public Data.Basic
import public Data.Symbolic
import public Data.Heap

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
  data Task : (h : Shape) -> (a : Type) -> Type where
    ---- Editors
    Edit   : (n : Name) -> (e : Editor h a) -> Task h a
    ---- Parallels
    Pair   : (t1 : Task h (Symbolic a)) -> (t2 : Task h (Symbolic b)) -> Task h (Symbolic a, Symbolic b)
    Done   : (v : Symbolic a) -> Task h (Symbolic a)
    Choose : (t1 : Task h (Symbolic a)) -> (t2 : Task h (Symbolic a)) -> Task h (Symbolic a)
    Fail   : Task h a
    ---- Steps
    Trans  : (f : Symbolic a' -> Symbolic a) -> (t2 : Task h (Symbolic a')) -> Task h (Symbolic a)
    Step   : (t1 : Task h (Symbolic a')) -> (c : Symbolic a' -> Task h (Symbolic a)) -> Task h (Symbolic a)
    ---- Asserts
    Assert : (p : Symbolic Bool) -> Task h (Symbolic Bool)
    Repeat : (t1 : Task h (Symbolic a)) -> Task h (Symbolic a)
    ---- Stores
    -- Share : {auto ok : IsBasic a} -> a -> Task h (Ref h a)
    Assign : {a : Type} -> {auto ok : IsBasic a} -> (v : Symbolic a) -> (r : Ref h (Symbolic a)) -> Task h (Symbolic ())

  public export
  data Editor : (h : Shape) -> (a : Type) -> Type where
    ---- Owned
    Enter  : {a : Type} -> Show a => {auto ok : IsBasic a} -> Editor h a  -- Also needs `Show` bacause semantics transforms `Enter` into an `Update`
    Update : {a : Type} -> Show a => {auto ok : IsBasic a} -> (v : a) -> Editor h a
    View   : {a : Type} -> Show a => {auto ok : IsBasic a} -> (v : a) -> Editor h a
    Select : (ts : List (Label, Task h a)) -> Editor h a
    ---- Shared
    Change : {a : Type} -> Show a => {auto ok : IsBasic a} -> (r : Ref h a) -> Editor h a
    Watch  : {a : Type} -> Show a => {auto ok : IsBasic a} -> (r : Ref h a) -> Editor h a

public export
data IsNormal : Task h a -> Type where
  EditIsNormal   : IsNormal (Edit (Named k) e)
  PairIsNormal   : IsNormal t1 -> IsNormal t2 -> IsNormal (Pair t1 t2)
  DoneIsNormal   : IsNormal (Done v)
  ChooseIsNormal : IsNormal t1 -> IsNormal t2 -> IsNormal (Choose t1 t2)
  FailIsNormal   : IsNormal Fail
  TransIsNormal  : IsNormal t2 -> IsNormal (Trans f t2)
  StepIsNormal   : IsNormal t1 -> IsNormal (Step t1 c)

---- Inputs & Options ----------------------------------------------------------

---- Real inputs

public export
data Real : Type where
  Value : {a' : Type} -> {auto ok' : IsBasic a'} -> (v : a') -> Real

---- Dummy inputs

public export
data Dummy : Type where
  Placeholder : (a' : Type) -> {auto ok' : IsBasic a'} -> Dummy

public export
Eq Dummy where
  (==) (Placeholder a {ok'=ok_a}) (Placeholder b {ok'=ok_b}) with (decBasic ok_a ok_b)
    (==) (Placeholder a {ok'=ok_a}) (Placeholder a {ok'=ok_a}) | Yes Refl = True
    (==) (Placeholder a {ok'=ok_a}) (Placeholder b {ok'=ok_b}) | No _ = False

symbolInjective : {auto ok_a : IsBasic a} -> {auto ok_b : IsBasic b} -> (Placeholder a = Placeholder b) -> (ok_a = ok_b)
symbolInjective {ok_a=ok} {ok_b=ok} Refl = Refl

public export
DecEq Dummy where
  decEq (Placeholder a {ok'=ok_a}) (Placeholder b {ok'=ok_b}) with (decBasic ok_a ok_b)
    decEq (Placeholder a {ok'=ok_a}) (Placeholder a {ok'=ok_a}) | Yes Refl = Yes Refl
    decEq (Placeholder a {ok'=ok_a}) (Placeholder b {ok'=ok_b}) | No cntr = No (cntr . symbolInjective)

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
dummify : Input Real -> Input Dummy
dummify (Insert k (Value {a'} _)) = Insert k (Placeholder a')
dummify (Option n l)              = Option n l
