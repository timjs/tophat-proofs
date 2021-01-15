module Task.Proofs.Inputs

import Helpers
import Control.Monad.State
import Data.Either
import Data.List
import Data.List.Elem
import Task.Error
import Task.Syntax
import Task.Observe
import Task.Run
import Task.Proofs.Lemmas

import Data.Vect

%default total

--------------------------------------------------------------------------------

inputIsHandled : (t : Task h a) -> IsNormal t => (i : Input Concrete) -> (s : State h) -> Elem (dummify i) (inputs t) -> IsRight (handle t i s)
inputIsHandled t s i elem = ?inputIsHandled_rhs

--------------------------------------------------------------------------------

pairNotRight : {t1 : Task h a} -> {n1 : IsNormal t1} -> {t2 : Task h b} -> {n2 : IsNormal t2} -> {s : State h} -> {i : Input Concrete}
  -> Not (IsRight (handle t1 @{n1} i s)) /\ Not (IsRight (handle t2 @{n2} i s))
  -> Not (IsRight (handle (Pair t1 t2) @{PairIsNormal n1 n2} i s))
pairNotRight (cntr1, cntr2) prf with (handle t1 i s)
  pairNotRight (cntr1, cntr2) prf | Right (t1', s', d') = cntr1 ItIsRight
  pairNotRight (cntr1, cntr2) prf | Left  _ with (handle t2 i s)
    pairNotRight (cntr1, cntr2) prf | Left  _ | Right (t2', s', d') = cntr2 ItIsRight
    pairNotRight (cntr1, cntr2) prf | Left  _ | Left _ = absurd prf

chooseNotRight : {t1 : Task h a} -> {n1 : IsNormal t1} -> {t2 : Task h a} -> {n2 : IsNormal t2} -> {s : State h} -> {i : Input Concrete}
  -> Not (IsRight (handle t1 @{n1} i s)) /\ Not (IsRight (handle t2 @{n2} i s))
  -> Not (IsRight (handle (Choose t1 t2) @{ChooseIsNormal n1 n2} i s))
chooseNotRight (cntr1, cntr2) prf with (handle t1 i s)
  chooseNotRight (cntr1, cntr2) prf | Right (t1', s', d') = cntr1 ItIsRight
  chooseNotRight (cntr1, cntr2) prf | Left  _ with (handle t2 i s)
    chooseNotRight (cntr1, cntr2) prf | Left  _ | Right (t2', s', d') = cntr2 ItIsRight
    chooseNotRight (cntr1, cntr2) prf | Left  _ | Left _ = absurd prf

-- transInjective : {e1 : a' -> a} -> {t2 : Task h a'} -> {n2 : IsNormal t2} -> {s : State h} -> {i : Input Concrete}
--   -> IsRight (handle (Trans e1 t2) @{TransIsNormal n2} i s)
--   -> IsRight (handle t2 i s)
-- transInjective prf with (handle (Trans e1 t2) i s)
--   transInjective prf | Right (t2', s') = ?transInjective_right
--   transInjective prf | Left x = ?transInjective_left

transNotRight : {t2 : Task h a} -> {n2 : IsNormal t2} -> {s : State h} -> {i : Input Concrete}
  -> Not (IsRight (handle t2 i s))
  -> Not (IsRight (handle (Trans e1 t2) @{TransIsNormal n2} i s))
transNotRight cntr prf with (handle t2 i s)
  transNotRight cntr prf | Right _ = cntr ItIsRight
  transNotRight cntr prf | Left  _ = absurd prf

stepRight : {t1 : Task h a} -> {n1 : IsNormal t1} -> {s : State h} -> {i : Input Concrete}
  -> IsRight (handle t1 i s)
  -> IsRight (handle (Step t1 e2) @{StepIsNormal n1} i s)
stepRight prf with (handle t1 i s)
  stepRight prf | Right (t1', s', d') = ItIsRight
  stepRight prf | Left  _ = absurd prf

stepNotRight : {t1 : Task h a} -> {n1 : IsNormal t1} -> {s : State h} -> {i : Input Concrete}
  -> Not (IsRight (handle t1 i s))
  -> Not (IsRight (handle (Step t1 e2) @{StepIsNormal n1} i s))
stepNotRight cntr prf with (handle t1 i s)
  stepNotRight cntr prf | Right _ = cntr ItIsRight
  stepNotRight cntr prf | Left  _ = absurd prf

handleIsPossible : (t : Task h a) -> IsNormal t => (i : Input Concrete) -> (s : State h) -> IsRight (handle t i s) -> Elem (dummify i) (inputs t)
---- Modifiable editors
handleIsPossible (Edit (Named k) (Enter @{ok})) @{EditIsNormal} (Insert k' (Value @{ok'} v')) s prf with (k ?= k')
  handleIsPossible (Edit (Named k) (Enter @{ok})) @{EditIsNormal} (Insert k  (Value @{ok'} v')) s prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit (Named k) (Enter @{ok})) @{EditIsNormal} (Insert k  (Value @{ok } v')) s prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit (Named k) (Enter @{ok})) @{EditIsNormal} (Insert k  (Value @{ok'} v')) s prf | Yes Refl | No  cntr = absurd prf
  handleIsPossible (Edit (Named k) (Enter @{ok})) @{EditIsNormal} (Insert k' (Value @{ok'} v')) s prf | No cntr = absurd prf
handleIsPossible (Edit (Named k) (Enter @{ok})) @{EditIsNormal} (Decide n' l) s prf = absurd prf
handleIsPossible (Edit (Named k) (Update @{ok} v)) @{EditIsNormal} (Insert k' (Value @{ok'} v')) s prf with (k ?= k')
  handleIsPossible (Edit (Named k) (Update @{ok} v)) @{EditIsNormal} (Insert k  (Value @{ok'} v')) s prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit (Named k) (Update @{ok} v)) @{EditIsNormal} (Insert k  (Value @{ok } v')) s prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit (Named k) (Update @{ok} v)) @{EditIsNormal} (Insert k  (Value @{ok'} v')) s prf | Yes Refl | No  cntr = absurd prf
  handleIsPossible (Edit (Named k) (Update @{ok} v)) @{EditIsNormal} (Insert k' (Value @{ok'} v')) s prf | No cntr = absurd prf
handleIsPossible (Edit (Named k) (Update @{ok} v)) @{EditIsNormal} (Decide n' l) s prf = absurd prf
handleIsPossible (Edit (Named k) (Change @{ok} r)) @{EditIsNormal} (Insert k' (Value @{ok'} v)) s prf with (k ?= k')
  handleIsPossible (Edit (Named k) (Change @{ok} r)) @{EditIsNormal} (Insert k  (Value @{ok'} v)) s prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit (Named k) (Change @{ok} r)) @{EditIsNormal} (Insert k  (Value @{ok } v)) s prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit (Named k) (Change @{ok} r)) @{EditIsNormal} (Insert k  (Value @{ok'} v)) s prf | Yes Refl | No  cntr = absurd prf
  handleIsPossible (Edit (Named k) (Change @{ok} r)) @{EditIsNormal} (Insert k' (Value @{ok'} v)) s prf | No cntr = absurd prf
handleIsPossible (Edit (Named k) (Change @{ok} r)) @{EditIsNormal} (Decide n' l) s prf = absurd prf
---- View-only editors
handleIsPossible (Edit (Named k) (View v)) (Insert k' c) s prf with (k ?= k')
  handleIsPossible (Edit (Named k) (View v)) (Insert k  c) s prf | Yes Refl = absurd prf
  handleIsPossible (Edit (Named k) (View v)) (Insert k' c) s prf | No cntr = absurd prf
handleIsPossible (Edit (Named k) (View v)) (Decide n' l) s prf = absurd prf
handleIsPossible (Edit (Named k) (Watch r)) (Insert k' c) s prf with (k ?= k')
  handleIsPossible (Edit (Named k) (Watch r)) (Insert k  c) s prf | Yes Refl = absurd prf
  handleIsPossible (Edit (Named k) (Watch r)) (Insert k' c) s prf | No cntr = absurd prf
handleIsPossible (Edit (Named k) (Watch r)) (Decide n' l) s prf = absurd prf
---- Paring
handleIsPossible (Pair t1 t2) @{PairIsNormal n1 n2} i s prf with (isItRight (handle t1 i s))
  handleIsPossible (Pair t1 t2) @{PairIsNormal n1 n2} i s prf | Yes prf1 = let rec = handleIsPossible t1 i s prf1 in elemInAppend (Left rec)
  handleIsPossible (Pair t1 t2) @{PairIsNormal n1 n2} i s prf | No cntr1 with (isItRight (handle t2 i s))
    handleIsPossible (Pair t1 t2) @{PairIsNormal n1 n2} i s prf | No cntr1 | Yes prf2 = let rec = handleIsPossible t2 i s prf2 in elemInAppend (Right rec)
    handleIsPossible (Pair t1 t2) @{PairIsNormal n1 n2} i s prf | No cntr1 | No cntr2 = let not = pairNotRight (cntr1, cntr2) in void (not prf)
---- Choosing
handleIsPossible (Choose t1 t2) @{ChooseIsNormal n1 n2} i s prf with (isItRight (handle t1 i s))
  handleIsPossible (Choose t1 t2) @{ChooseIsNormal n1 n2} i s prf | Yes prf1 = let rec = handleIsPossible t1 i s prf1 in elemInAppend (Left rec)
  handleIsPossible (Choose t1 t2) @{ChooseIsNormal n1 n2} i s prf | No cntr1 with (isItRight (handle t2 i s))
    handleIsPossible (Choose t1 t2) @{ChooseIsNormal n1 n2} i s prf | No cntr1 | Yes prf2 = let rec = handleIsPossible t2 i s prf2 in elemInAppend (Right rec)
    handleIsPossible (Choose t1 t2) @{ChooseIsNormal n1 n2} i s prf | No cntr1 | No cntr2 = let not = chooseNotRight (cntr1, cntr2) in void (not prf)
---- Transforming
handleIsPossible (Trans f t2) @{TransIsNormal n2} i s prf with (isItRight (handle t2 i s))
  handleIsPossible (Trans f t2) @{TransIsNormal n2} i s prf | Yes prf2 = let rec = handleIsPossible t2 i s prf2 in rec
  handleIsPossible (Trans f t2) @{TransIsNormal n2} i s prf | No cntr2 = let not = transNotRight cntr2 in void (not prf)
---- Stepping
handleIsPossible (Step t1 c) @{StepIsNormal n1} i s prf with (isItRight (handle t1 i s))
  handleIsPossible (Step t1 c) @{StepIsNormal n1} i s prf | Yes prf1 = let rec = handleIsPossible t1 i s prf1 in rec
  handleIsPossible (Step t1 c) @{StepIsNormal n1} i s prf | No cntr1 = let not = stepNotRight cntr1 in void (not prf)
---- Static tasks
handleIsPossible (Done v) i s prf = absurd prf
handleIsPossible Fail i s prf = absurd prf

--------------------------------------------------------------------------------

safe : (t : Task h a) -> IsNormal t => (i : Input Concrete) -> (s : State h) -> Elem (dummify i) (inputs t) <-> IsRight (handle t i s)
safe t i s = (inputIsHandled t i s, handleIsPossible t i s)
