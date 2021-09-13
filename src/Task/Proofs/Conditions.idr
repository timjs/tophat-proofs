module Task.Proofs.Conditions

import Helpers
import Data.List.Elem
import Task.Condition
import Task.Error
import Task.Input
import Task.Observe
import Task.Run
import Task.Syntax

-- finished_stays_finished :
--   (t : Task h a) -> IsNormal t =>
--   (s : Heap h) ->
--   IsJust (value t s) ->
--   (i : Input Concrete) -> Elem (dummify i) (inputs t) ->
--   (case interact t i s of
--     Right (n', s') => IsJust (value t' s') /\ IsCons (inputs t')
--     Left _ => Void)

-- finished_stays_finished :
--   (t : Task h a) -> IsNormal t => (s : Heap h) ->
--   IsJust (value t s) ->
--   (i : Input Concrete) -> Elem (dummify i) (inputs t) ->
--   (case interact t i s of
--     Right (n', s') => IsJust (value t' s') /\ IsCons (inputs t')
--     Left _ => Void)

-- recurringStaysRecurring : (t : Task h a) -> IsNormal t => (s : Heap h)
-- -> condition t s = Recurring
-- -> (i : Input Concrete) -> Elem (dummify i) (inputs t)
-- -> IsRight (interact t i s)
-- -- condition t' s' = Recurring
