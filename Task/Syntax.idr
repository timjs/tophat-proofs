module Task.Syntax

import public Task.Universe

%default total

---- Tasks ---------------------------------------------------------------------

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

mutual

  public export
  data Task : (h : Heap) -> (a : Ty) -> Type where
    ---- Editors
    Edit : {a : Ty} -> (n : Name) -> (e : Editor h a) -> Task h a
    ---- Parallels
    Pair : (t1 : Task h a) -> (t2 : Task h b) -> Task h (PAIR a b)
    Done : (v : typeOf a) -> Task h a
    Choose : (t1 : Task h a) -> (t2 : Task h a) -> Task h a
    Fail : Task h a
    ---- Steps
    Trans : (f : typeOf a' -> typeOf a) -> (t : Task h a') -> Task h a
    Step : (t : Task h a') -> (c : typeOf a' -> Task h a) -> Task h a
    ---- Asserts
    Assert : (b : Bool) -> Task h (PRIM BOOL)
    ---- Stores
    -- Share : IsBasic t => t -> Task h (Ref h t)
    Assign : IsBasic a => (v : typeOf a) -> (r : typeOf (REF h a)) -> Task h UNIT

  public export
  data Editor : (h : Heap) -> (a : Ty) -> Type where
    ---- Owned
    Enter : IsBasic a => Editor h a
    Update : IsBasic a => (v : typeOf a) -> Editor h a
    View : IsBasic a => (v : typeOf a) -> Editor h a
    Select : (ts : List (Label, Task h a)) -> Editor h a
    ---- Shared
    Change : IsBasic a => (r : typeOf (REF h a)) -> Editor h a
    Watch : IsBasic a => (r : typeOf (REF h a)) -> Editor h a

---- Inputs & Options ----------------------------------------------------------

---- Concrete inputs

public export
data Concrete : Type where
  AConcrete : {b : Ty} -> IsBasic b => Eq (typeOf b) => (v : typeOf b) -> Concrete

---- Dummy inputs

public export
data Dummy : Type where
  ADummy : (b : Ty) -> IsBasic b => Dummy

public export
Eq Dummy where
  (==) (ADummy a) (ADummy b) with (decEq a b)
    (==) (ADummy a) (ADummy a) | (Yes Refl)  = True
    (==) (ADummy a) (ADummy b) | (No contra) = False

---- Input actions

public export
data Action k
  = AEnter k
  | ASelect Label

public export
Eq k => Eq (Action k) where
  (==) (AEnter x)  (AEnter x')  = x == x'
  (==) (ASelect l) (ASelect l') = l == l'
  (==) _             _               = False

---- Full inputs

public export
data Input k
  = AInput Name (Action k)

public export
Eq k => Eq (Input k) where
  (==) (AInput n a)  (AInput n' a')  = n == n' && a == a'
  (==) _             _               = False

---- Options

public export
data Option
  = AOption Name Label

export
fromOption : Option -> Input b
fromOption (AOption n l) = AInput n (ASelect l)