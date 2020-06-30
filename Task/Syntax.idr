module Task.Syntax

-- import Task.Universe


---- Basic types ---------------------------------------------------------------

interface Basic t where

Basic Bool where
Basic Int where
Basic String where
(Basic a, Basic b) => Basic (a, b) where

---- Heaps ---------------------------------------------------------------------

||| Heap shape
public export
data Heap
  ||| Single integer
  = Single

||| References into the heap
public export
data Ref : Heap -> Type -> Type where
  ||| Location of single integer
  Loc : Ref Single Int

||| Concrete heap of certain shape
export
data State : Heap -> Type where
  ||| Value of single integer
  Saved : Int -> State Single

export
read : Ref h t -> State h -> t
read Loc (Saved x) = x

---- Tasks ---------------------------------------------------------------------

export
Label : Type
Label = String

public export
data Name
  = Unnamed
  | Named Nat

mutual

  public export
  data Task : (h : Heap) -> (t : Type) -> Type where
    ---- Editors
    Edit : {t : Type} -> Name -> Editor h t -> Task h t
    ---- Parallels
    Pair : Task h a -> Task h b -> Task h (a, b)
    Done : t -> Task h t
    Choose : Task h t -> Task h t -> Task h t
    Fail : Task h t
    ---- Steps
    Trans : (a -> t) -> Task h a -> Task h t
    Step : Task h a -> (a -> Task h t) -> Task h t
    ---- Asserts
    Assert : Bool -> Task h Bool
    ---- Stores
    -- Share : (Basic t) => t -> Task h (Ref h t)
    Assign : (Basic a) => a -> Ref h a -> Task h ()

  public export
  data Editor : (h : Heap) -> (t : Type) -> Type where
    ---- Owned
    Enter : (Basic t) => Editor h t
    Update : (Basic t) => t -> Editor h t
    View : (Basic t) => t -> Editor h t
    Select : List (Label, Task h t) -> Editor h t
    ---- Shared
    Change : (Basic t) => Ref h t -> Editor h t
    Watch : (Basic t) => Ref h t -> Editor h t

---- Inputs & Options ----------------------------------------------------------

public export
data Concrete : Type where
  AConcrete : Basic b => b -> Concrete

public export
data Dummy : Type where
  ADummy : (b : Type) -> Basic b => Dummy

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

public export
data Option
  = AOption Name Label

export
fromOption : Option -> Input b
fromOption (AOption n l) = IOption n l
