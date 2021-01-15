module Task.Input

import Helpers
import public Data.Name
import public Type.Basic

---- Concrete values -----------------------------------------------------------

public export
data Concrete : Type where
  Value : IsBasic a' => (v : a') -> Concrete

---- Abstract values -----------------------------------------------------------

public export
data Abstract : Type where
  Dummy : (0 a' : Type) -> IsBasic a' => Abstract

dummyInjective : {ok1 : IsBasic a} -> {ok2 : IsBasic b} -> (Dummy a = Dummy b) -> (ok1 = ok2)
dummyInjective Refl = Refl

public export
Eq Abstract where
  (==) (Dummy a1 @{ok1}) (Dummy a2 @{ok2}) with (decBasic ok1 ok2)
    (==) (Dummy a  @{ok})  (Dummy a  @{ok})  | Yes Refl = True
    (==) (Dummy a1 @{ok1}) (Dummy a2 @{ok2}) | No  _    = False

public export
DecEq Abstract where
  decEq (Dummy a1 @{ok1}) (Dummy a2 @{ok2}) with (decBasic ok1 ok2)
    decEq (Dummy a  @{ok})  (Dummy a  @{ok})  | Yes Refl = Yes Refl
    decEq (Dummy a1 @{ok1}) (Dummy a2 @{ok2}) | No  cntr = No (cntr . dummyInjective)

---- Inputs --------------------------------------------------------------------

||| Inputs are parametrised over concrete or abstract values
public export
data Input v
  = Insert Id v
  | Decide Id Label

insertInjective : (Insert k v = Insert k x) -> (v = x)
insertInjective Refl = Refl

pickInjective : (Decide k l = Decide k x) -> (l = x)
pickInjective Refl = Refl

public export
Eq v => Eq (Input v) where
  (==) (Insert k x) (Insert k' x') = k == k' && x == x'
  (==) (Decide k l) (Decide k' l') = k == k' && l == l'
  (==) _            _              = False

public export
DecEq v => DecEq (Input v) where
  decEq (Insert k x) (Insert k' x') = ?input_decEq_insert
  decEq (Decide n l) (Decide n' l') = ?input_decEq_pick
  decEq _            _              = ?action_decEq_rest

public export
dummify : Input Concrete -> Input Abstract
dummify (Insert k (Value {a'} v)) = Insert k (Dummy a')
dummify (Decide k l)              = Decide k l
