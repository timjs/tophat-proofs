module Task

-- import Task.Universe
import Data.SortedMap


---- Basic types ---------------------------------------------------------------

interface Basic t where

Basic Bool where
Basic Int where
Basic String where
(Basic a, Basic b) => Basic (a, b) where

---- Heaps ---------------------------------------------------------------------

data Heap
  = GlobalHeap

data Store : Heap -> Type -> Type where
  Loc : Store h t

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
    ---- Stores
    Share : (Basic t) => t -> Task h (Store h t)
    Assign : (Basic a) => a -> Store h a -> Task h ()

  data Editor : (h : Heap) -> (t : Type) -> Type where
    ---- Owned
    Enter : (Basic t) => Editor h t
    Update : (Basic t) => t -> Editor h t
    View : (Basic t) => t -> Editor h t
    Select : SortedMap Label (Task h t) -> Editor h t
    ---- Shared
    Change : (Basic t) => Store h t -> Editor h t
    Watch : (Basic t) => Store h t -> Editor h t
