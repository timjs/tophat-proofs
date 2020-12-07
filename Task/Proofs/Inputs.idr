module Task.Proofs.Inputs

import Helpers
import Control.Monad.State
import Data.Either
import Data.List
import Data.List.Elem
import Task.Syntax
import Task.Observations
import Task.Semantics
import Task.Proofs.Lemmas

import Data.Vect

%default total

--------------------------------------------------------------------------------

inputIsHandled : (t : Task h a) -> IsNormal t => (s : State h) -> (i : Input Concrete) -> Elem (dummify i) (inputs t (get s)) -> IsRight (handle t i s)
inputIsHandled t i elem = ?inputIsHandled_rhs

--------------------------------------------------------------------------------

pairNotRight : {auto n1 : IsNormal t1} -> {auto n2 : IsNormal t2}
  -> Not (IsRight (handle t1 @{n1} i s)) /\ Not (IsRight (handle t2 @{n2} i s))
  -> Not (IsRight (handle (Pair t1 t2) @{PairIsNormal n1 n2} i s))

chooseNotRight : {auto n1 : IsNormal t1} -> {auto n2 : IsNormal t2}
  -> Not (IsRight (handle t1 @{n1} i s)) /\ Not (IsRight (handle t2 @{n2} i s))
  -> Not (IsRight (handle (Choose t1 t2) @{ChooseIsNormal n1 n2} i s))

transInjective : {e1 : a' -> a} -> {t2 : Task h a'} -> {auto n2 : IsNormal t2} -> {s : State h} -> {i : Input Concrete}
  -> IsRight (handle (Trans e1 t2) @{TransIsNormal n2} i s)
  -> IsRight (handle t2 i s)
transInjective prf with (handle (Trans e1 t2) i s)
  transInjective prf | Right (t2', s') = ?transInjective_right
  transInjective prf | Left x = ?transInjective_left

transNotRight : {t2 : Task h a} -> {auto n2 : IsNormal t2} -> {s : State h} -> {i : Input Concrete}
  -> Not (IsRight (handle t2 i s))
  -> Not (IsRight (handle (Trans e1 t2) @{TransIsNormal n2} i s))
transNotRight cntr prf with (handle t2 i s)
  transNotRight cntr prf | Right (t2', s') = ?transNotRight_right
  transNotRight cntr prf | Left x = absurd prf

handleIsPossible : (t : Task h a) -> {auto n : IsNormal t} -> (s : State h) -> (i : Input Concrete) -> IsRight (handle t i s) -> Elem (dummify i) (inputs t (get s))
---- Modifiable editors
handleIsPossible (Edit n (Enter {a} {ok})) s (Insert n' (Value {a'} {ok'} v')) prf with (n ?= n')
  handleIsPossible (Edit n (Enter {a} {ok})) s (Insert n (Value {a'} {ok'} v')) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Enter {a} {ok})) s (Insert n (Value {a'=a} {ok'=ok} v')) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Enter {a} {ok})) s (Insert n (Value {a'} {ok'} v'))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Enter {a} {ok})) s (Insert n' (Value {a'} {ok'} v')) prf | No cntr = absurd prf
handleIsPossible (Edit n (Enter {a} {ok})) s (Decide n' l) prf = absurd prf
handleIsPossible (Edit n (Update {a} {ok} v)) s (Insert n' (Value {a'} {ok'} v')) prf with (n ?= n')
  handleIsPossible (Edit n (Update {a} {ok} v)) s (Insert n (Value {a'} {ok'} v')) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Update {a} {ok} v)) s (Insert n (Value {a'=a} {ok'=ok} v')) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Update {a} {ok} v)) s (Insert n (Value {a'} {ok'} v'))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Update {a} {ok} v)) s (Insert n' (Value {a'} {ok'} v')) prf | No cntr = absurd prf
handleIsPossible (Edit n (Update {a} {ok} v)) s (Decide n' l) prf = absurd prf
handleIsPossible (Edit n (Change {a} {ok} r)) s (Insert n' (Value {a'} {ok'} v)) prf with (n ?= n')
  handleIsPossible (Edit n (Change {a} {ok} r)) s (Insert n (Value {a'} {ok'} v)) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Change {a} {ok} r)) s (Insert n (Value {a'=a} {ok'=ok} v)) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Change {a} {ok} r)) s (Insert n (Value {a'} {ok'} v))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Change {a} {ok} r)) s (Insert n' (Value {a'} {ok'} v)) prf | No cntr = absurd prf
handleIsPossible (Edit n (Change {a} {ok} r)) s (Decide n' l) prf = absurd prf
---- Select-only editor
handleIsPossible (Edit n (Select ts)) s (Insert n' v) prf = absurd prf
handleIsPossible t@(Edit n (Select ts)) s (Decide n' l) prf with (n ?= n')
  --> `t` should be in scope because of type signature...
  handleIsPossible t@(Edit n (Select ts)) s (Decide n l) prf | Yes Refl with (lookup l ts)
    handleIsPossible t@(Edit n (Select ts)) s (Decide n l) prf | Yes Refl | Nothing = absurd prf
    handleIsPossible t@(Edit n (Select ts)) s (Decide n l) prf | Yes Refl | Just x with ((n, l) `elem` options t)
      handleIsPossible t@(Edit n (Select ts)) s (Decide n l) prf | Yes Refl | Just x | True  = ?handleIsPossible_select_elem
      handleIsPossible t@(Edit n (Select ts)) s (Decide n l) prf | Yes Refl | Just x | False = ?handleIsPossible_select_noelem
  handleIsPossible t@(Edit n (Select ts)) s (Decide n' l) prf | No cntr  = absurd prf
---- View-only editors
handleIsPossible (Edit n (View v)) s (Insert n' c) prf with (n ?= n')
  handleIsPossible (Edit n (View v)) s (Insert n c) prf | Yes Refl = absurd prf
  handleIsPossible (Edit n (View v)) s (Insert n' c) prf | No cntr = absurd prf
handleIsPossible (Edit n (View v)) s (Decide n' l) prf = absurd prf
handleIsPossible (Edit n (Watch r)) s (Insert n' c) prf with (n ?= n')
  handleIsPossible (Edit n (Watch r)) s (Insert n c) prf | Yes Refl = absurd prf
  handleIsPossible (Edit n (Watch r)) s (Insert n' c) prf | No cntr = absurd prf
handleIsPossible (Edit n (Watch r)) s (Decide n' l) prf = absurd prf
---- Paring
handleIsPossible (Pair t1 t2) i s prf with (isItRight (handle t1 i s))
  handleIsPossible (Pair t1 t2) i s prf | Yes prf1 = let rec = handleIsPossible t1 i s prf1 in elemInAppend (Left rec)
  handleIsPossible (Pair t1 t2) i s prf | No cntr1 with (isItRight (handle t2 i s))
    handleIsPossible (Pair t1 t2) i s prf | No cntr1 | Yes prf2 = let rec = handleIsPossible t2 i s prf2 in elemInAppend (Right rec)
    handleIsPossible (Pair t1 t2) i s prf | No cntr1 | No cntr2 = let not = pairNotRight (cntr1, cntr2) in void (not prf)
---- Choosing
handleIsPossible (Choose t1 t2) i s prf with (isItRight (handle t1 i s))
  handleIsPossible (Choose t1 t2) i s prf | Yes prf1 = let rec = handleIsPossible t1 i s prf1 in elemInAppend (Left rec)
  handleIsPossible (Choose t1 t2) i s prf | No cntr1 with (isItRight (handle t2 i s))
    handleIsPossible (Choose t1 t2) i s prf | No cntr1 | Yes prf2 = let rec = handleIsPossible t2 i s prf2 in elemInAppend (Right rec)
    handleIsPossible (Choose t1 t2) i s prf | No cntr1 | No cntr2 = let not = chooseNotRight (cntr1, cntr2) in void (not prf)
---- Transforming
handleIsPossible (Trans f t2) i s prf with (isItRight (handle t2 i s))
  handleIsPossible (Trans f t2) i s prf | Yes prf2 = let rec = handleIsPossible t2 i s prf2 in rec
  handleIsPossible (Trans f t2) i s prf | No cntr2 = let not = transNotRight cntr2 in void (not prf)
---- Stepping
handleIsPossible (Step t1 c) i s prf with (isItRight (handle t1 i s))
  handleIsPossible (Step t1 c) i s prf | Yes prf1 = let rec = handleIsPossible t1 i s prf1 in elemInAppend (Left rec)
  handleIsPossible (Step t1 c) i s prf | No cntr1 with (value t1 s)
    handleIsPossible (Step t1 c) i s prf | No cntr1 | Just v1 = ?handleIsPossible_step_value
    handleIsPossible (Step t1 c) i s prf | No cntr1 | Nothing = ?handleIsPossible_step_novalue
---- Static tasks
handleIsPossible (Done v) i s prf = absurd prf
handleIsPossible Fail i s prf = absurd prf
handleIsPossible (Assert p) i s prf = absurd prf
handleIsPossible (Assign v r) i s prf = absurd prf

--------------------------------------------------------------------------------

safe : (t : Task h a) -> {auto n : IsNormal t} -> (s : State h) -> (i : Input Concrete) -> Elem (dummify i) (inputs t (get s)) <-> IsRight (handle t i s)
safe t i s = (inputIsHandled t i s, handleIsPossible t i s)
