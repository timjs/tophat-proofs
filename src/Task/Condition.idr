module Task.Condition

import Helpers
import Task.Syntax
import Task.Observe
import Task.Proofs.Failing

%default total

data Condition : Task h a -> Type where
  Failing   : {t : Task h a} -> {auto n : IsNormal t} -> {s : Heap h} -> (IsTrue  (failing t), IsNothing (value t s), IsNil  (inputs t)) -> Condition t
  Finished  : {t : Task h a} -> {auto n : IsNormal t} -> {s : Heap h} -> (IsFalse (failing t), IsJust    (value t s), IsNil  (inputs t)) -> Condition t
  Recurring : {t : Task h a} -> {auto n : IsNormal t} -> {s : Heap h} -> (IsFalse (failing t), IsJust    (value t s), IsCons (inputs t)) -> Condition t
  Running   : {t : Task h a} -> {auto n : IsNormal t} -> {s : Heap h} -> (IsFalse (failing t), IsNothing (value t s), IsCons (inputs t)) -> Condition t
  Stuck     : {t : Task h a} -> {auto n : IsNormal t} -> {s : Heap h} -> (IsFalse (failing t), IsNothing (value t s), IsNil  (inputs t)) -> Condition t

||| Covering function for the `Condition` view.
condition : (t : Task h a) -> IsNormal t => (s : Heap h) -> Condition t
condition t s with (isItTrue (failing t))
  condition t s | Yes yes_f = let (nope_v, nope_i) = failingMeansNoInteraction t s yes_f in Failing (yes_f, nope_v, nope_i)
  condition t s | No nope_f with (isItJust (value t s), isItCons (inputs t))
    condition t s | No nope_f | (Yes yes_v, No nope_i) = Finished (notTrueIsFalse nope_f, yes_v, notConsIsNil nope_i)
    condition t s | No nope_f | (Yes yes_v, Yes yes_i) = Recurring (notTrueIsFalse nope_f, yes_v, yes_i)
    condition t s | No nope_f | (No nope_v, Yes yes_i) = Running (notTrueIsFalse nope_f, notJustIsNothing nope_v, yes_i)
    condition t s | No nope_f | (No nope_v, No nope_i) = Stuck (notTrueIsFalse nope_f, notJustIsNothing nope_v, notConsIsNil nope_i)
