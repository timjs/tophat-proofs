module Task.State

import Data.Stream
import Data.Symbolic
import public Data.Some
import public Data.Heap

%default total

---- State ---------------------------------------------------------------------

export
State : Shape -> Type
State h = (Stream Nat, Heap h)

export
empty : State None
empty = (iterate S 0, Empty)

export
wrap : Heap h -> State h
wrap h = (iterate S 0, h)

export
bools : State Triple
bools = (iterate S 0, Saved3 (Value True) (Value True) (Value True))

export
get : State h -> Heap h
get = snd

export
modify : (Heap h -> Heap h) -> State h -> State h
modify f (ns, s) = (ns, f s)

export
fresh : State h -> (Nat, State h)
fresh (n :: ns, s) = (n, (ns, s))

---- Delta ---------------------------------------------------------------------

public export
Delta : Shape -> Type
Delta h = List (Some (Ref h))
