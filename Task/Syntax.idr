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
  data Task : (h : Heap) -> (t : Ty) -> Type where
    ---- Editors
    Edit : {t : Ty} -> Name -> Editor h t -> Task h t
    ---- Parallels
    Pair : Task h a -> Task h b -> Task h (PAIR a b)
    Done : typeOf t -> Task h t
    Choose : Task h t -> Task h t -> Task h t
    Fail : Task h t
    ---- Steps
    Trans : (typeOf a -> typeOf t) -> Task h a -> Task h t
    Step : Task h a -> (typeOf a -> Task h t) -> Task h t
    ---- Asserts
    Assert : Bool -> Task h (PRIM BOOL)
    ---- Stores
    -- Share : IsBasic t => t -> Task h (Ref h t)
    Assign : IsBasic a => typeOf a -> typeOf (REF h a) -> Task h UNIT

  public export
  data Editor : (h : Heap) -> (t : Ty) -> Type where
    ---- Owned
    Enter : IsBasic t => Editor h t
    Update : IsBasic t => typeOf t -> Editor h t
    View : IsBasic t => typeOf t -> Editor h t
    Select : List (Label, Task h t) -> Editor h t
    ---- Shared
    Change : IsBasic t => typeOf (REF h t) -> Editor h t
    Watch : IsBasic t => typeOf (REF h t) -> Editor h t

---- Inputs & Options ----------------------------------------------------------

---- Concrete inputs

public export
data Concrete : Type where
  AConcrete : IsBasic b => typeOf b -> Concrete

---- Dummy inputs

public export
data Dummy : Type where
  ADummy : (b : Ty) -> IsBasic b => Dummy

export
Eq Dummy where
  (==) (ADummy a) (ADummy b) with (decEq a b)
    (==) (ADummy a) (ADummy a) | (Yes Refl)  = True
    (==) (ADummy a) (ADummy b) | (No contra) = False

---- Input actions

public export
data Input k
  = IEnter Nat k
  | IOption Name Label

public export
ISelect : Nat -> Label -> Input b
ISelect n l = IOption (Named n) l

public export
IPreselect : Label -> Input b
IPreselect l = IOption Unnamed l

export
Eq k => Eq (Input k) where
  (==) (IEnter i x)  (IEnter i' x')  = i == i' && x == x'
  (==) (IOption n l) (IOption n' l') = n == n' && l == l'
  (==) _             _               = False

---- Options

public export
data Option
  = AOption Name Label

export
fromOption : Option -> Input b
fromOption (AOption n l) = IOption n l
