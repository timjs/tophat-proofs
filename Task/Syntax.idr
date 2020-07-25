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
  (==) (Named i) (Named i') = i == i'
  (==) _         _          = False

export
Uninhabited (Unnamed = Named i) where
  uninhabited Refl impossible

export
namedInjective : (Named i = Named j) -> (i = j)
namedInjective Refl = Refl

public export
DecEq Name where
  decEq (Unnamed) (Unnamed)  = Yes Refl
  decEq (Named i) (Named i') with (i ?= i')
    decEq (Named i) (Named i)  | Yes Refl = Yes Refl
    decEq (Named i) (Named i') | No contra = No (contra . namedInjective)
  decEq (Unnamed) (Named i)  = No absurd
  decEq (Named i) (Unnamed)  = No (negEqSym absurd)

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

symbolicInjective : {auto ok_a : IsBasic a} -> {auto ok_b : IsBasic b} -> (Symbol a = Symbol b) -> (ok_a = ok_b)
symbolicInjective {ok_a=ok} {ok_b=ok} Refl = Refl

public export
DecEq Symbolic where
  decEq (Symbol a {ok'=ok_a}) (Symbol b {ok'=ok_b}) with (decBasic ok_a ok_b)
    decEq (Symbol a {ok'=ok_a}) (Symbol a {ok'=ok_a}) | Yes Refl = Yes Refl
    decEq (Symbol a {ok'=ok_a}) (Symbol b {ok'=ok_b}) | No cntr = No (cntr . symbolicInjective)

---- Input actions

public export
data Action k
  = Insert k
  | Decide Label

enterInjective : (Insert k = Insert x) -> (k = x)
enterInjective Refl = Refl

selectInjective : (Decide l = Decide x) -> (l = x)
selectInjective Refl = Refl

public export
Eq k => Eq (Action k) where
  (==) (Insert x)  (Insert x')  = x == x'
  (==) (Decide l) (Decide l') = l == l'
  (==) _           _            = False

public export
DecEq k => DecEq (Action k) where
  decEq (Insert x)  (Insert x')  with (x ?= x')
    decEq (Insert x)  (Insert x)  | Yes Refl = Yes Refl
    decEq (Insert x)  (Insert x') | No cntr = No (cntr . enterInjective)
  decEq (Decide l) (Decide l') with (l ?= l')
    decEq (Decide l) (Decide l)  | Yes Refl = Yes Refl
    decEq (Decide l) (Decide l') | No cntr = No (cntr . selectInjective)
  decEq _           _            = ?action_decEq_rest

---- Full inputs

public export
Input : Type -> Type
Input k = (Name, Action k)
-- data Input k
--   = AInput Name (Action k)

public export
dummify : Input Concrete -> Input Symbolic
dummify (n, Insert (Value {a'} _)) = (n, Insert (Symbol a'))
dummify (n, Decide l)                 = (n, Decide l)

-- public export
-- Eq k => Eq (Input k) where
--   (==) (AInput n a)  (AInput n' a')  = n == n' && a == a'
--   (==) _             _               = False

-- public export
-- DecEq k => DecEq (Input k) where
--   decEq (AInput n a) (AInput n' a') with (n ?= n', a ?= a')
--     decEq (AInput n a) (AInput n' a') | with_pat = ?input_decEq_rest

---- Options

public export
Option : Type
Option = (Name, Label)
-- data Option
--   = AOption Name Label


export
fromOption : Option -> Input b
fromOption (n, l) = (n, Decide l)