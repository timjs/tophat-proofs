module Task.Syntax

import Helpers
import public Data.Name
import public Type.Basic
import public Task.State

%default total

---- Tasks & Editors -----------------------------------------------------------

mutual

  public export
  data Task : (h : Shape) -> (a : Type) -> Type where
    ---- Editors
    Edit   : (n : Name) -> (e : Editor h a) -> Task h a
    ---- Parallels
    Pair   : (t1 : Task h a) -> (t2 : Task h b) -> Task h (a, b)
    Done   : (v : a) -> Task h a
    Choose : (t1 : Task h a) -> (t2 : Task h a) -> Task h a
    Test   : Bool -> Task h a -> Task h a -> Task h a
    Fail   : Task h a
    ---- Steps
    Trans  : (f : a' -> a) -> (t2 : Task h a') -> Task h a --<< f : Symbolic a' -> Simulation a
    Step   : (t1 : Task h a') -> (c : a' -> Task h a) -> Task h a --<< c : Symbolic a' -> Simulation (Task h a)
    ---- Asserts
    Assert : (p : Bool) -> Task h Bool
    Repeat : (t1 : Task h a) -> Task h a
    ---- Stores
    -- Share : IsBasic a => a -> Task h (Ref h a)
    Assign : IsBasic a => (v : a) -> (r : Ref h a) -> Task h ()

  public export
  data Editor : (h : Shape) -> (a : Type) -> Type where
    ---- Owned
    Enter  : IsBasic a => Show a => Eq a => Editor h a  -- Also needs `Show` bacause semantics transforms `Enter` into an `Update`
    Update : IsBasic a => Show a => Eq a => (v : a) -> Editor h a
    View   : IsBasic a => Show a => Eq a => (v : a) -> Editor h a
    Select : (ts : List (Label, Task h a)) -> Editor h a
    ---- Shared
    Change : IsBasic a => Show a => Eq a => (r : Ref h a) -> Editor h a
    Watch  : IsBasic a => Show a => Eq a => (r : Ref h a) -> Editor h a

---- Normalised predicate ------------------------------------------------------

public export
data IsNormal : Task h a -> Type where
  EditIsNormal   : IsNormal (Edit (Named k) e)
  PairIsNormal   : IsNormal t1 -> IsNormal t2 -> IsNormal (Pair t1 t2)
  DoneIsNormal   : IsNormal (Done v)
  ChooseIsNormal : IsNormal t1 -> IsNormal t2 -> IsNormal (Choose t1 t2)
  FailIsNormal   : IsNormal Fail
  TransIsNormal  : IsNormal t2 -> IsNormal (Trans f t2)
  StepIsNormal   : IsNormal t1 -> IsNormal (Step t1 c)

---- Derived -------------------------------------------------------------------

public export
Guard : List (Bool, Task h a) -> Task h a
Guard [] = Fail
Guard ((p, t) :: bs) = Test p t (Guard bs)
