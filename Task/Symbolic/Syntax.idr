module Task.Symbolic.Syntax

import Helpers
import public Data.Name
import public Data.Symbolic
import public Type.Basic
import public Task.State

%default total

---- Tasks & Editors -----------------------------------------------------------

mutual

  public export
  data Task : (h : Shape) -> (a : Type) -> Type where
    ---- Editors
    Edit   : (n : Name) -> (e : Editor h (Symbolic a)) -> Task h (Symbolic a)
    Select : (n : Name) -> (t1 : Task h (Symbolic a')) -> (bs : List (Label, (Symbolic a') -> Task h (Symbolic a))) -> Task h (Symbolic a)
    ---- Parallels
    Pair   : (t1 : Task h (Symbolic a)) -> (t2 : Task h (Symbolic b)) -> Task h (Symbolic (a, b))
    Done   : (v : Symbolic a) -> Task h (Symbolic a)
    Choose : (t1 : Task h (Symbolic a)) -> (t2 : Task h (Symbolic a)) -> Task h (Symbolic a)
    Fail   : Task h a
    ---- Steps
    Trans  : (e1 : Symbolic a' -> Symbolic a) -> (t2 : Task h (Symbolic a')) -> Task h (Symbolic a) --<< f : Symbolic a' -> Simulation (Symbolic a)
    Step   : (t1 : Task h (Symbolic a')) -> (e2 : Symbolic a' -> Task h (Symbolic a)) -> Task h (Symbolic a) --<< c : Symbolic a' -> Simulation (Task h (Symbolic a))
    Repeat : (t1 : Task h (Symbolic a)) -> Task h (Symbolic a)
    ---- Asserts
    Test   : Symbolic Bool -> Task h (Symbolic a) -> Task h (Symbolic a) -> Task h (Symbolic a)
    Assert : (p : Symbolic Bool) -> Task h (Symbolic Bool)
    ---- Stores
    -- Share : IsBasic a => a -> Task h (Ref h a)
    Assign : IsBasic a => Eq a => (v : Symbolic a) -> (r : Ref h (Symbolic a)) -> Task h (Symbolic ())

  public export
  data Editor : (h : Shape) -> (a : Type) -> Type where
    ---- Owned
    Enter  : IsBasic a => Show a => Eq a => Editor h (Symbolic a)  -- Also needs `Show` bacause semantics transforms `Enter` into an `Update`
    Update : IsBasic a => Show a => Eq a => (v : Symbolic a) -> Editor h (Symbolic a)
    View   : IsBasic a => Show a => Eq a => (v : Symbolic a) -> Editor h (Symbolic a)
    ---- Shared
    Change : IsBasic a => Show a => Eq a => (r : Ref h (Symbolic a)) -> Editor h (Symbolic a)  -- Needs `Eq` to save in `Pack`
    Watch  : IsBasic a => Show a => Eq a => (r : Ref h (Symbolic a)) -> Editor h (Symbolic a)

---- Normalised predicate ------------------------------------------------------

public export
data IsNormal : Task h a -> Type where
  EditIsNormal   : IsNormal (Edit (Named k) e)
  SelectIsNormal : IsNormal t1 -> IsNormal (Select (Named k) t1 ts)
  PairIsNormal   : IsNormal t1 -> IsNormal t2 -> IsNormal (Pair t1 t2)
  DoneIsNormal   : IsNormal (Done v)
  ChooseIsNormal : IsNormal t1 -> IsNormal t2 -> IsNormal (Choose t1 t2)
  FailIsNormal   : IsNormal Fail
  TransIsNormal  : IsNormal t2 -> IsNormal (Trans f t2)
  StepIsNormal   : IsNormal t1 -> IsNormal (Step t1 c)
