module Task.Heap

%default total

---- Types ---------------------------------------------------------------------

||| The shape of a heap.
|||
||| Determines the type of data stored at every memory location.
||| Heaps have a length `k` and every location has a certain type `t` from the universe `u`.
Shape : Type
Shape = List Type

||| Hetrogenious heap indexed by a `Shape`.
|||
||| `Nil` is the empty heap.
||| `(::)` allocates a value `a` of type `t` on a heap `as` of shape `ts`
||| to construct a heap of shape `t :: ts`.
|||
||| Note: corresponds to the definition of `Data.HVect`.
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
data Ref : t -> (ts : Shape) -> Type where
  Here  : Ref t (t :: ts)
  There : (l : Ref t ts) -> Ref t (t' :: ts)

---- Operations ----------------------------------------------------------------

alloc : t' -> Heap ts -> (Ref t' (t' :: ts), Heap (t' :: ts))
alloc y [] = (Here, [y])
alloc y xs = (Here, y :: xs)

read : Ref t ts -> Heap ts -> t
read _         []        impossible
read (Here)    (x :: _)  = x
read (There l) (_ :: xs) = read l xs

write : Ref t ts -> t -> Heap ts -> Heap ts
write _         _ []        impossible
write (Here)    y (_ :: xs) = y :: xs
write (There l) y (x :: xs) = x :: write l y xs
