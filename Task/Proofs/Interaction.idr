module Task.Proofs.Interaction

import Helpers
import Data.Maybe
import Data.List
import Data.List.Quantifiers
import Task.Syntax
import Task.Observations
import Task.Proofs.Lemmas

%default total

---- Interaction ---------------------------------------------------------------

interaction : (t : Task h b) -> (s : State h) -> (failing t = True) -> (value t s = Nothing) /\ (inputs t s = [])
interaction (Edit n (Enter))     s Refl impossible
interaction (Edit n (Update _))  s Refl impossible
interaction (Edit n (View _))    s Refl impossible
interaction (Edit n (Select ts)) s prf  = let prf_all = hoist_all {p=failing . snd} {l=ts} prf
                                              prf_emp = all_true_empties_filter prf_all
                                          in  rewrite prf_emp in (Refl, Refl)
interaction (Edit n (Change _))  s Refl impossible
interaction (Edit n (Watch _))   s Refl impossible
interaction (Pair t1 t2)         s p_f12 with (failing t1 ?= True, failing t2 ?= True)
  interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, Yes p_f2) with (interaction t1 s p_f1, interaction t2 s p_f2)
    interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, Yes p_f2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in
                                                                                                       --> `rewrite p_v2` is not needed because of definiiton of `<&>`
                                                                                                       rewrite p_i1 in
                                                                                                       rewrite p_i2 in (Refl, Refl)
  interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) with (failing t2)
    interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | True = absurd (no_f2 Refl)
    interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False with (failing t1)
      interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False | True = absurd p_f12
      interaction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False | False = absurd p_f12
  interaction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) with (failing t1)
    interaction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | True = absurd (no_f1 Refl)
    interaction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False with (failing t2)
      interaction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False | True = absurd p_f12
      interaction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False | False = absurd p_f12
  interaction (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) with (failing t1)
    interaction (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) | True = absurd (no_f1 Refl)
    interaction (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) | False = absurd p_f12
interaction (Done v)             s Refl impossible
interaction (Choose t1 t2)       s prf with (and_split failing t1 t2 prf)
  interaction (Choose t1 t2)       s prf | (prf_1, prf_2) with (interaction t1 s prf_1, interaction t2 s prf_2)
    interaction (Choose t1 t2)       s prf | (prf_1, prf_2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in
                                                                                               rewrite p_v2 in
                                                                                               rewrite p_i1 in
                                                                                               rewrite p_i2 in (Refl, Refl)
interaction Fail                 s Refl = (Refl, Refl)
interaction (Trans f t2)         s prf with (interaction t2 s prf)
  interaction (Trans f t2)         s prf | (p_v2, p_i2) = (rewrite p_v2 in Refl, p_i2)
interaction (Step t1 c)          s prf with (interaction t1 s prf)
  interaction (Step t1 c)          s prf | (p_v1, p_i1) = (Refl, rewrite p_i1 in rewrite p_v1 in Refl)
interaction (Assert y)           s Refl impossible
interaction (Assign v r)         s Refl impossible

lemma : ((failing t = True) -> (value t s = Nothing) /\ (inputs t s = [])) -> ((IsJust (value t s) \/ NonEmpty (inputs t s)) -> (failing t = False))
-- lemma imp prf with (implyIsNotReverse imp)
--   lemma imp prf | rev = ?h
lemma imp (Left  prf) = ?lemma_rhs_1
lemma imp (Right prf) = ?lemma_rhs_2

-- lemma imp = \prf =>
--   let rev = implyIsNotReverse imp
--       unp = orIsNotAnd prf
--    in ?lemma_rhs

usefulness : (t : Task h b) -> (s : State h) -> (IsJust (value t s) \/ NonEmpty (inputs t s)) -> (failing t = False)
usefulness t s (Left prf) = ?usefulness_rhs_1
usefulness t s (Right prf) = ?usefulness_rhs_2