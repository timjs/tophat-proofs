module Task.Proofs.Usefulness

import Helpers
import Data.Maybe
import Data.List
import Task.Syntax
import Task.Observations
-- import Task.Semantics
import Task.Proofs.Lemmas

%default total

--------------------------------------------------------------------------------

||| For every task `t` in state `s` we know that either of the two options hold
||| * the task fails; or
||| * the task has a value or it is possible to interact with it.
usefulness : {s : State h} -> (t : Task h a) -> (failing t = True) <> (IsJust (value t s) \/ NonEmpty (inputs t s))
usefulness (Edit n Enter)       = Right (uninhabited, Right IsNonEmpty)
usefulness (Edit n (Update v))  = Right (uninhabited, Right IsNonEmpty)
usefulness (Edit n (View v))    = Right (uninhabited, Left ItIsJust)
usefulness (Edit n (Select ts)) = Right (?f1, ?u1)
usefulness (Edit n (Change r))  = Right (uninhabited, Right IsNonEmpty)
usefulness (Edit n (Watch r))   = Right (uninhabited, Left ItIsJust)
usefulness (Pair t1 t2)         = ?usefulness_rhs_2
usefulness (Done v)             = Right (uninhabited, Left ItIsJust)
usefulness (Choose t1 t2)       = ?usefulness_rhs_4
usefulness Fail                 = Left (Refl, andNotIsNotOr (uninhabited, uninhabited)) --absurd (Left IsNonEmpty))
usefulness (Trans f t2)         with (usefulness {s} t2)
  usefulness (Trans f t2)       | Left  (yes, nop) = Left  (yes, ?usefulness_rhs_6_rhs_1)
  usefulness (Trans f t2)       | Right (nop, yes) = Right (nop, ?usefulness_rhs_6_rhs_2)
usefulness (Step t1 c)          = ?usefulness_rhs_7
usefulness (Assert p)           = Right (uninhabited, Left ItIsJust)
usefulness (Assign v r)         = Right (uninhabited, Left ItIsJust)

||| Corollary of usefulness: when task `t` is failing, it has no value and it has no inputs.
interaction : {s : State h} -> (t : Task h a) -> (failing t = True) -> (value t s = Nothing) /\ (inputs t s = [])
interaction t prf with (usefulness {s} t)
  interaction t prf | Right (nop, yes) = absurd (nop prf)
  interaction t prf | Left  (yes, nop) =
    let (no_value, no_input) = notOrIsAndNot nop
     in (notJustIsNothing no_value, notNonEmptyIsNil no_input)
