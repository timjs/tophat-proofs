module Task

import Data.SortedMap
-- import Task.Universe


---- Basic types ---------------------------------------------------------------

interface Basic t where

Basic Bool where
Basic Int where
Basic String where
(Basic a, Basic b) => Basic (a, b) where

---- Heaps ---------------------------------------------------------------------

||| Heap shape
data Heap
  ||| Single integer
  = Single

||| References into the heap
data Ref : Heap -> Type -> Type where
  ||| Location of single integer
  Loc : Ref Single Int

||| Concrete heap of certain shape
data State : Heap -> Type where
  ||| Value of single integer
  Saved : Int -> State Single

export
read : Ref h t -> State h -> t
read Loc (Saved x) = x

---- Tasks ---------------------------------------------------------------------

Label : Type
Label = String

data Name
  = Unnamed
  | Named Nat

mutual

  data Task : (h : Heap) -> (t : Type) -> Type where
    ---- Editors
    Edit : Name -> Editor h t -> Task h t
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

  data Editor : (h : Heap) -> (t : Type) -> Type where
    ---- Owned
    Enter : (Basic t) => Editor h t
    Update : (Basic t) => t -> Editor h t
    View : (Basic t) => t -> Editor h t
    Select : SortedMap Label (Task h t) -> Editor h t
    ---- Shared
    Change : (Basic t) => Ref h t -> Editor h t
    Watch : (Basic t) => Ref h t -> Editor h t
