module Data.Heap

import Helpers
import Decidable.Equality

%default total

---- Heaps ---------------------------------------------------------------------

||| Heap shape
public export
data Shape
  = ||| Nothing
    None
  | ||| Single integer
    Single

Uninhabited (None = Single) where
  uninhabited Refl impossible

export
DecEq Shape where
  decEq (None)   (None)   = Yes Refl
  decEq (None)   (Single) = No absurd
  decEq (Single) (Single) = Yes Refl
  decEq (Single) (None)   = No (negEqSym absurd)

||| References into the heap
public export
data Ref : Shape -> Type -> Type where
  ||| Location of single integer
  Loc : Ref Single Int

export
Eq1 (Ref h) where
  eq1 Loc Loc = True

export
Eq (Ref h a) where
  Loc == Loc = True

||| Concrete heap of certain shape
public export
data Heap : Shape -> Type where
  ||| Empty heap
  Empty : Heap None
  ||| Value of single integer
  Saved : Int -> Heap Single

export
read : Ref h t -> Heap h -> t
read Loc (Saved x) = x

export
write : t -> Ref h t -> Heap h -> Heap h
write y Loc (Saved x) = Saved y

{-
---- Types ---------------------------------------------------------------------

||| The shape of a heap.
|||
||| Determines the type of data stored at every memory location.
||| Heaps have a length `k` and every location has a certain type `t` from the universe `u`.
public export
Shape : Type
Shape = List Type

||| Hetrogenious heap indexed by a `Shape`.
|||
||| `Nil` is the empty heap.
||| `(::)` allocates a value `a` of type `t` on a heap `as` of shape `ts`
||| to construct a heap of shape `t :: ts`.
|||
||| Note: corresponds to the definition of `Data.HVect`.
public export
data Heap : (ts : Shape) -> Type where
  Nil  : Heap []
  (::) : (x : t) -> (xs : Heap ts) -> Heap (t :: ts)

||| Location on the heap.
|||
||| A value of type `Ref t ts` corresponds to a proof that a value of type `t`
||| is stored in a heap of shape `ts`.
||| `Here` means it is stored at this location.
||| `There` means it is stored a bit further on the heap.
|||
||| Note: corresponds to the definition of `Data.Vect.Elem`.
public export
data Ref : t -> (ts : Shape) -> Type where
  Here  : Ref t (t :: ts)
  There : (l : Ref t ts) -> Ref t (t' :: ts)

---- Operations ----------------------------------------------------------------

public export
alloc : t' -> Heap ts -> (Ref t' (t' :: ts), Heap (t' :: ts))
alloc y [] = (Here, [y])
alloc y xs = (Here, y :: xs)

public export
read : Ref t ts -> Heap ts -> t
read _         []        impossible
read (Here)    (x :: _)  = x
read (There l) (_ :: xs) = read l xs

public export
write : Ref t ts -> t -> Heap ts -> Heap ts
write _         _ []        impossible
write (Here)    y (_ :: xs) = y :: xs
write (There l) y (x :: xs) = x :: write l y xs
-}
