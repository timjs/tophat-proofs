module Task.Condition

import Helpers
import Task.Syntax
import Task.Observations
import Task.Proofs.Interaction

%default total

data Condition : Task h a -> Type where
  Failing   : {t : Task h a} -> {auto s : State h} -> IsTrue (failing t)                           -> Condition t
  Finished  : {t : Task h a} -> {auto s : State h} -> (IsJust    (value t s), IsNil  (inputs t s)) -> Condition t
  Recurring : {t : Task h a} -> {auto s : State h} -> (IsJust    (value t s), IsCons (inputs t s)) -> Condition t
  Running   : {t : Task h a} -> {auto s : State h} -> (IsNothing (value t s), IsCons (inputs t s)) -> Condition t
  Stuck     : {t : Task h a} -> {auto s : State h} -> (IsNothing (value t s), IsNil  (inputs t s)) -> Condition t

||| Covering function for the `Condition` view.
condition : (t : Task h a) -> {s : State h} -> Condition t
condition t {s} with (isItTrue (failing t))
  condition t {s} | Yes yes_f = Failing yes_f
  condition t {s} | No nope_f with (isItJust (value t s), isItCons (inputs t s))
    condition t {s} | No nope_f | (Yes yes_v, No nope_i) = Finished (yes_v, notConsIsNil nope_i)
    condition t {s} | No nope_f | (Yes yes_v, Yes yes_i) = Recurring (yes_v, yes_i)
    condition t {s} | No nope_f | (No nope_v, Yes yes_i) = Running (notJustIsNothing nope_v, yes_i)
    condition t {s} | No nope_f | (No nope_v, No nope_i) = Stuck (notJustIsNothing nope_v, notConsIsNil nope_i)