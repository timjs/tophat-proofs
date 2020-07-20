module Task.Proofs.Inputs

import Helpers
import Control.Monad.State
import Data.Either
import Data.List
import Task.Syntax
import Task.Observations
import Task.Semantics
import Task.Proofs.Lemmas

import Data.Vect

%default total

--------------------------------------------------------------------------------

inputIsHandled : (t : Task h a) -> (s : State h) -> (i : Input Concrete) -> Elem (dummify i) (inputs t s) -> IsRight (handle t s i)
inputIsHandled t i elem = ?inputIsHandled_rhs

--------------------------------------------------------------------------------

pairNotRight : Not (IsRight (handle t1 s i)) /\ Not (IsRight (handle t2 s i)) -> Not (IsRight (handle (Pair t1 t2) s i))

chooseNotRight : Not (IsRight (handle t1 s i)) /\ Not (IsRight (handle t2 s i)) -> Not (IsRight (handle (Choose t1 t2) s i))

transInjective : {e1 : a' -> a} -> {t2 : Task h a'} -> {s : State h} -> {i : Input Concrete} -> IsRight (handle (Trans e1 t2) s i) -> IsRight (handle t2 s i)
transInjective prf with (handle (Trans e1 t2) s i)
  transInjective prf | Right (t2', s') = ?transInjective_right
  transInjective prf | Left x = ?transInjective_left

transNotRight : {t2 : Task h a} -> {s : State h} -> {i : Input Concrete} -> Not (IsRight (handle t2 s i)) -> Not (IsRight (handle (Trans e1 t2) s i))
transNotRight cntr prf with (handle t2 s i)
  transNotRight cntr prf | Right (t2', s') = ?transNotRight_right
  transNotRight cntr prf | Left x = absurd prf

handleIsPossible : (t : Task h a) -> (s : State h) -> (i : Input Concrete) -> IsRight (handle t s i) -> Elem (dummify i) (inputs t s)
---- Modifiable editors
handleIsPossible (Edit n (Enter {a} {ok})) s (n', Insert (Value {a'} {ok'} v')) prf with (n ?= n')
  handleIsPossible (Edit n (Enter {a} {ok})) s (n , Insert (Value {a'} {ok'} v')) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Enter {a} {ok})) s (n , Insert (Value {a'=a} {ok'=ok} v')) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Enter {a} {ok})) s (n , Insert (Value {a'} {ok'} v'))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Enter {a} {ok})) s (n', Insert (Value {a'} {ok'} v')) prf | No cntr = absurd prf
handleIsPossible (Edit n (Enter {a} {ok})) s (n', Decide l) prf = absurd prf
handleIsPossible (Edit n (Update {a} {ok} v)) s (n', Insert (Value {a'} {ok'} v')) prf with (n ?= n')
  handleIsPossible (Edit n (Update {a} {ok} v)) s (n , Insert (Value {a'} {ok'} v')) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Update {a} {ok} v)) s (n , Insert (Value {a'=a} {ok'=ok} v')) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Update {a} {ok} v)) s (n , Insert (Value {a'} {ok'} v'))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Update {a} {ok} v)) s (n', Insert (Value {a'} {ok'} v')) prf | No cntr = absurd prf
handleIsPossible (Edit n (Update {a} {ok} v)) s (n', Decide l) prf = absurd prf
handleIsPossible (Edit n (Change {a} {ok} r)) s (n', Insert (Value {a'} {ok'} v)) prf with (n ?= n')
  handleIsPossible (Edit n (Change {a} {ok} r)) s (n , Insert (Value {a'} {ok'} v)) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Change {a} {ok} r)) s (n , Insert (Value {a'=a} {ok'=ok} v)) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Change {a} {ok} r)) s (n , Insert (Value {a'} {ok'} v))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Change {a} {ok} r)) s (n', Insert (Value {a'} {ok'} v)) prf | No cntr = absurd prf
handleIsPossible (Edit n (Change {a} {ok} r)) s (n', Decide l) prf = absurd prf
---- Select-only editor
handleIsPossible (Edit n (Select ts)) s (n', Insert v) prf = absurd prf
handleIsPossible t@(Edit n (Select ts)) s (n', Decide l) prf with (n ?= n')
  --> `t` should be in scope because of type signature...
  handleIsPossible t@(Edit n (Select ts)) s (n , Decide l) prf | Yes Refl with (lookup l ts)
    handleIsPossible t@(Edit n (Select ts)) s (n , Decide l) prf | Yes Refl | Nothing = absurd prf
    handleIsPossible t@(Edit n (Select ts)) s (n , Decide l) prf | Yes Refl | Just x with ((n, l) `elem` options t)
      handleIsPossible t@(Edit n (Select ts)) s (n , Decide l) prf | Yes Refl | Just x | True  = ?handleIsPossible_select_elem
      handleIsPossible t@(Edit n (Select ts)) s (n , Decide l) prf | Yes Refl | Just x | False = ?handleIsPossible_select_noelem
  handleIsPossible t@(Edit n (Select ts)) s (n', Decide l) prf | No cntr  = absurd prf
---- View-only editors
handleIsPossible (Edit n (View v)) s (n', Insert c) prf with (n ?= n')
  handleIsPossible (Edit n (View v)) s (n , Insert c) prf | Yes Refl = absurd prf
  handleIsPossible (Edit n (View v)) s (n', Insert c) prf | No cntr = absurd prf
handleIsPossible (Edit n (View v)) s (n', Decide l) prf = absurd prf
handleIsPossible (Edit n (Watch r)) s (n', Insert c) prf with (n ?= n')
  handleIsPossible (Edit n (Watch r)) s (n , Insert c) prf | Yes Refl = absurd prf
  handleIsPossible (Edit n (Watch r)) s (n', Insert c) prf | No cntr = absurd prf
handleIsPossible (Edit n (Watch r)) s (n', Decide l) prf = absurd prf
---- Paring
handleIsPossible (Pair t1 t2) s i prf with (isItRight (handle t1 s i))
  handleIsPossible (Pair t1 t2) s i prf | Yes prf1 = let rec = handleIsPossible t1 s i prf1 in elemInAppend (Left rec)
  handleIsPossible (Pair t1 t2) s i prf | No cntr1 with (isItRight (handle t2 s i))
    handleIsPossible (Pair t1 t2) s i prf | No cntr1 | Yes prf2 = let rec = handleIsPossible t2 s i prf2 in elemInAppend (Right rec)
    handleIsPossible (Pair t1 t2) s i prf | No cntr1 | No cntr2 = let not = pairNotRight (cntr1, cntr2) in void (not prf)
---- Choosing
handleIsPossible (Choose t1 t2) s i prf with (isItRight (handle t1 s i))
  handleIsPossible (Choose t1 t2) s i prf | Yes prf1 = let rec = handleIsPossible t1 s i prf1 in elemInAppend (Left rec)
  handleIsPossible (Choose t1 t2) s i prf | No cntr1 with (isItRight (handle t2 s i))
    handleIsPossible (Choose t1 t2) s i prf | No cntr1 | Yes prf2 = let rec = handleIsPossible t2 s i prf2 in elemInAppend (Right rec)
    handleIsPossible (Choose t1 t2) s i prf | No cntr1 | No cntr2 = let not = chooseNotRight (cntr1, cntr2) in void (not prf)
---- Transforming
handleIsPossible (Trans f t2) s i prf with (isItRight (handle t2 s i))
  handleIsPossible (Trans f t2) s i prf | Yes prf2 = let rec = handleIsPossible t2 s i prf2 in rec
  handleIsPossible (Trans f t2) s i prf | No cntr2 = let not = transNotRight cntr2 in void (not prf)
---- Stepping
handleIsPossible (Step t1 c) s i prf with (isItRight (handle t1 s i))
  handleIsPossible (Step t1 c) s i prf | Yes prf1 = let rec = handleIsPossible t1 s i prf1 in elemInAppend (Left rec)
  handleIsPossible (Step t1 c) s i prf | No cntr1 with (value t1 s)
    handleIsPossible (Step t1 c) s i prf | No cntr1 | Just v1 = ?handleIsPossible_step_value
    handleIsPossible (Step t1 c) s i prf | No cntr1 | Nothing = ?handleIsPossible_step_novalue
---- Static tasks
handleIsPossible (Done v) s i prf = absurd prf
handleIsPossible Fail s i prf = absurd prf
handleIsPossible (Assert p) s i prf = absurd prf
handleIsPossible (Assign v r) s i prf = absurd prf

--------------------------------------------------------------------------------

safe : (t : Task h a) -> (s : State h) -> (i : Input Concrete) -> Elem (dummify i) (inputs t s) <-> IsRight (handle t s i)
safe t s i = (inputIsHandled t s i, handleIsPossible t s i)
