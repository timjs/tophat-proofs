module Task.Proofs.Inputs

import Helpers
import Control.Monad.State
import Data.Either
import Data.List
import Task.Syntax
import Task.Observations
import Task.Semantics
import Task.Proofs.Lemmas

%default total

--------------------------------------------------------------------------------

handles : State h -> Task h a -> Input Concrete -> Either NotApplicable (Task h a)
handles s t i = evalState (handle t i) s

inputIsHandled : {s : State h} -> (t : Task h a) -> (i : Input Concrete) -> Elem (dummify i) (inputs t s) -> IsRight (handles s t i)
inputIsHandled t i elem = ?inputIsHandled_rhs

handleIsPossible : {auto s : State h} -> (t : Task h a) -> (i : Input Concrete) -> IsRight (handles s t i) -> Elem (dummify i) (inputs t s)
---- Modifiable editors
handleIsPossible (Edit n (Enter {a} {ok})) (n', AEnter (AConcrete {a'} {ok'} v')) prf with (n ?= n')
  handleIsPossible (Edit n (Enter {a} {ok})) (n , AEnter (AConcrete {a'} {ok'} v')) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Enter {a} {ok})) (n , AEnter (AConcrete {a'=a} {ok'=ok} v')) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Enter {a} {ok})) (n , AEnter (AConcrete {a'} {ok'} v'))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Enter {a} {ok})) (n', AEnter (AConcrete {a'} {ok'} v')) prf | No cntr = absurd prf
handleIsPossible (Edit n (Enter {a} {ok})) (n', ASelect l) prf = absurd prf
handleIsPossible (Edit n (Update {a} {ok} v)) (n', AEnter (AConcrete {a'} {ok'} v')) prf with (n ?= n')
  handleIsPossible (Edit n (Update {a} {ok} v)) (n , AEnter (AConcrete {a'} {ok'} v')) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Update {a} {ok} v)) (n , AEnter (AConcrete {a'=a} {ok'=ok} v')) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Update {a} {ok} v)) (n , AEnter (AConcrete {a'} {ok'} v'))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Update {a} {ok} v)) (n', AEnter (AConcrete {a'} {ok'} v')) prf | No cntr = absurd prf
handleIsPossible (Edit n (Update {a} {ok} v)) (n', ASelect l) prf = absurd prf
handleIsPossible (Edit n (Change {a} {ok} r)) (n', AEnter (AConcrete {a'} {ok'} v)) prf with (n ?= n')
  handleIsPossible (Edit n (Change {a} {ok} r)) (n , AEnter (AConcrete {a'} {ok'} v)) prf | Yes Refl with (decBasic ok ok')
    handleIsPossible (Edit n (Change {a} {ok} r)) (n , AEnter (AConcrete {a'=a} {ok'=ok} v)) prf | Yes Refl | Yes Refl = Here
    handleIsPossible (Edit n (Change {a} {ok} r)) (n , AEnter (AConcrete {a'} {ok'} v))      prf | Yes Refl | No cntr  = absurd prf
  handleIsPossible (Edit n (Change {a} {ok} r)) (n', AEnter (AConcrete {a'} {ok'} v)) prf | No cntr = absurd prf
handleIsPossible (Edit n (Change {a} {ok} r)) (n', ASelect l) prf = absurd prf
---- Select-only editor
handleIsPossible (Edit n (Select ts)) (n', AEnter v) prf = absurd prf
handleIsPossible t@(Edit n (Select ts)) (n', ASelect l) prf with (n ?= n')
  handleIsPossible t@(Edit n (Select ts)) (n , ASelect l) prf | Yes Refl with (lookup l ts)
    handleIsPossible t@(Edit n (Select ts)) (n , ASelect l) prf | Yes Refl | Nothing = absurd prf
    handleIsPossible t@(Edit n (Select ts)) (n , ASelect l) prf | Yes Refl | Just x  with ((n, l) `elem` options t)
      handleIsPossible t@(Edit n (Select ts)) (n , ASelect l) prf | Yes Refl | Just x  | True  = ?something_complicated_rhs_2_rhs_1
      handleIsPossible t@(Edit n (Select ts)) (n , ASelect l) prf | Yes Refl | Just x  | False = ?something_complicated_rhs_2_rhs_2
  handleIsPossible t@(Edit n (Select ts)) (n', ASelect l) prf | No cntr  = absurd prf
---- View-only editors
handleIsPossible (Edit n (View v)) (n', AEnter c) prf with (n ?= n')
  handleIsPossible (Edit n (View v)) (n , AEnter c) prf | Yes Refl = absurd prf
  handleIsPossible (Edit n (View v)) (n', AEnter c) prf | No cntr = absurd prf
handleIsPossible (Edit n (View v)) (n', ASelect l) prf = absurd prf
handleIsPossible (Edit n (Watch r)) (n', AEnter c) prf with (n ?= n')
  handleIsPossible (Edit n (Watch r)) (n , AEnter c) prf | Yes Refl = absurd prf
  handleIsPossible (Edit n (Watch r)) (n', AEnter c) prf | No cntr = absurd prf
handleIsPossible (Edit n (Watch r)) (n', ASelect l) prf = absurd prf
---- Combinators
handleIsPossible (Pair t1 t2)         (n', a) prf = ?handleIsPossible_rhs_2
handleIsPossible (Choose t1 t2) i prf with (handles s t1 i)
  handleIsPossible (Choose t1 t2) i prf | Left  e = ?handleIsPossible_rhs_4_rhs_1
  handleIsPossible (Choose t1 t2) i prf | Right x = ?handleIsPossible_rhs_4_rhs_2
-- handleIsPossible (Trans f t2)         i       prf = let rec = handleIsPossible t2 i prf in ?h
handleIsPossible (Trans f t2)         i       prf with (handles s t2 i)
  handleIsPossible (Trans f t2)         i       prf | Left  e = let rec = handleIsPossible t2 i in ?handleIsPossible_rhs_6_rhs
  handleIsPossible (Trans f t2)         i       prf | Right x = let rec = handleIsPossible t2 i in ?handleIsPossible_rhs_68_rhs

handleIsPossible (Step t1 c)          (n', a) prf = ?handleIsPossible_rhs_7
---- Static tasks
handleIsPossible (Done v)             (n', a) prf = absurd prf
handleIsPossible Fail                 (n', a) prf = absurd prf
handleIsPossible (Assert p)           (n', a) prf = absurd prf
handleIsPossible (Assign v r)         (n', a) prf = absurd prf



safe : {i : Input Concrete} -> {s : State h} -> (t : Task h a) -> Elem (dummify i) (inputs t s) <-> IsRight (handles s t i)
safe t = (inputIsHandled t i, handleIsPossible t i)
