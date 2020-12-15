module Task.State

import public Data.Basic
import public Data.Heap

---- State ---------------------------------------------------------------------

export
State : Shape -> Type
State h = (Stream Nat, Heap h)

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
