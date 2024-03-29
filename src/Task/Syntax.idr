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
    Edit   : (n : Name) -> (d : Editor h a) -> Task h a
    -- Select : (n : Name) -> (t1 : Task h a') -> (bs : List (Label, a' -> Task h a)) -> Task h a
    ---- Parallels
    Pair   : (t1 : Task h a) -> (t2 : Task h b) -> Task h (a, b)
    Done   : (v : a) -> Task h a
    Choose : (t1 : Task h a) -> (t2 : Task h a) -> Task h a
    Fail   : Task h a
    ---- Steps
    Trans  : (f : a' -> a) -> (t2 : Task h a') -> Task h a
    Step   : (t1 : Task h a') -> (e2 : a' -> Task h a) -> Task h a
    -- Repeat : (t1 : Task h a) -> Task h a
    ---- Asserts
    -- Assert : (p : Bool) -> Task h Bool
    ---- Stores
    -- Share : IsBasic a => a -> Task h (Ref h a)
    Assign : IsBasic a => Eq a => (v : a) -> (r : Ref h a) -> Task h ()

  public export
  data Editor : (h : Shape) -> (a : Type) -> Type where
    ---- Owned
    Enter  : IsBasic a => Show a => Eq a => Editor h a  -- Also needs `Show` bacause semantics transforms `Enter` into an `Update`
    Update : IsBasic a => Show a => Eq a => (v : a) -> Editor h a
    View   : IsBasic a => Show a => Eq a => (v : a) -> Editor h a
    ---- Shared
    Change : IsBasic a => Show a => Eq a => (r : Ref h a) -> Editor h a  -- Needs `Eq` to save in `Pack`
    Watch  : IsBasic a => Show a => Eq a => (r : Ref h a) -> Editor h a

public export
Branch : List (Bool, Task h a) -> Task h a
Branch [] = Fail
Branch ((b, t) :: ts) = if b then t else Branch ts

public export
Select : {n : Nat} -> Name -> Task h a -> Vect n (Label, a -> Task h b) -> Task h b
Select name t1 cs =
  (t1 `Pair` Edit name Enter) `Step` \(x, i) =>
  snd (index i cs) x

public export
Pick : {n : Nat} -> Name -> Vect n (Label, Task h a) -> Task h a
Pick name ts =
  Edit name Enter `Step` \i =>
  index i ts |> snd
  -- Select n (Done ()) (map (\(l, t) -> (l, const t)))

public export
Continue : Task h a' -> (a' -> Task h a) -> Task h a
Continue t1 e2 = Select Unnamed t1 ["Continue" ~> e2]

public export
Assert : Bool -> Task h Bool
Assert p = Done p

public export
covering
Repeat : Task h a -> Task h a
Repeat t1 = Select Unnamed t1 ["Repeat" ~> \_ => Repeat t1, "Exit" ~> \x => Done x]

---- Normalised predicate ------------------------------------------------------

public export
data IsNormal : Task h a -> Type where
  EditIsNormal   : IsNormal (Edit (Named k) d)
  PairIsNormal   : IsNormal t1 -> IsNormal t2 -> IsNormal (Pair t1 t2)
  DoneIsNormal   : IsNormal (Done v)
  ChooseIsNormal : IsNormal t1 -> IsNormal t2 -> IsNormal (Choose t1 t2)
  FailIsNormal   : IsNormal Fail
  TransIsNormal  : IsNormal t2 -> IsNormal (Trans e1 t2)
  StepIsNormal   : IsNormal t1 -> IsNormal (Step t1 e2)

public export
SelectIsNormal : IsNormal t1 -> IsNormal (Select (Named k) t1 cs)
SelectIsNormal n1 = StepIsNormal (PairIsNormal n1 EditIsNormal)

public export
PickIsNormal : IsNormal (Pick (Named k) cs)
PickIsNormal = StepIsNormal EditIsNormal --SelectIsNormal DoneIsNormal


---- Static predicate ----------------------------------------------------------

-- public export
-- data IsStaticEditor : Editor h a -> Type where

public export
data IsStatic : Task h a -> Type where
  -- EditIsStatic  : IsStatic (Edit (Named k) d)
  UpdateIsStatic : IsBasic a => Show a => Eq a => {0 v : a} -> IsStatic (Edit (Named k) (Update v))
  ViewIsStatic   : IsBasic a => Show a => Eq a => {0 v : a} -> IsStatic (Edit (Named k) (View v))
  ChangeIsStatic : IsBasic a => Show a => Eq a => {0 r : Ref h a} -> IsStatic (Edit (Named k) (Change r))
  WatchIsStatic  : IsBasic a => Show a => Eq a => {0 r : Ref h a} -> IsStatic (Edit (Named k) (Watch r))
  PairIsStatic   : IsStatic t1 -> IsStatic t2 -> IsStatic (Pair t1 t2)
  DoneIsStatic   : IsStatic (Done v)
  TransIsStatic  : IsStatic t2 -> IsStatic (Trans e1 t2)
