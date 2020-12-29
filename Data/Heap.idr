module Data.Heap

import Helpers
import Data.Fin
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
  | ||| Three bools
    Triple

Uninhabited (None = Single) where
  uninhabited Refl impossible
Uninhabited (None = Triple) where
  uninhabited Refl impossible
Uninhabited (Single = Triple) where
  uninhabited Refl impossible

export
DecEq Shape where
  decEq (None)   (None)   = Yes Refl
  decEq (None)   (Single) = No absurd
  decEq (None)   (Triple) = No absurd
  decEq (Single) (Single) = Yes Refl
  decEq (Single) (None)   = No (negEqSym absurd)
  decEq (Single) (Triple) = No absurd
  decEq (Triple) (Triple) = Yes Refl
  decEq (Triple) (None)   = No (negEqSym absurd)
  decEq (Triple) (Single) = No (negEqSym absurd)

||| References into the heap
public export
data Ref : Shape -> Type -> Type where
  ||| Location of single integer
  Loc : Ref Single Int
  ||| Index of one of three bools
  Idx : Fin 3 -> Ref Triple Bool

export
Eq (Ref h a) where
  Loc    == Loc    = True
  Idx i1 == Idx i2 = i1 == i2
  Loc    == _      = False
  Idx _  == _      = False

export
Eq1 (Ref h) where
  eq1 a b = a == b

||| Concrete heap of certain shape
public export
data Heap : Shape -> Type where
  ||| Empty heap
  Empty : Heap None
  ||| Value of single integer
  Saved1 : Int -> Heap Single
  |||
  Saved3 : Bool -> Bool -> Bool -> Heap Triple

export
read : Ref h t -> Heap h -> t
read Loc     (Saved1 x)     = x
read (Idx 0) (Saved3 x _ _) = x
read (Idx 1) (Saved3 _ y _) = y
read (Idx 2) (Saved3 _ _ z) = z

export
write : t -> Ref h t -> Heap h -> Heap h
write x' Loc (Saved1 x) = Saved1 x'
write x' (Idx 0) (Saved3 x y z) = (Saved3 x' y  z )
write y' (Idx 1) (Saved3 x y z) = (Saved3 x  y' z )
write z' (Idx 2) (Saved3 x y z) = (Saved3 x  y  z')

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
