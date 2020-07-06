module Task.Proofs.Interaction

import Helpers
import Data.Maybe
import Data.List.Quantifiers
import Task.Syntax
import Task.Observations
import Task.Proofs.Lemmas

%default total

---- Interaction ---------------------------------------------------------------

fail_no_inter : (t : Task h b) -> (s : State h) -> (failing t = True) -> (value t s = Nothing) /\ (inputs t s = [])
fail_no_inter (Edit n (Enter))     s Refl impossible
fail_no_inter (Edit n (Update _))  s Refl impossible
fail_no_inter (Edit n (View _))    s Refl impossible
fail_no_inter (Edit n (Select ts)) s prf  = let prf_all = hoist_all {p=failing . snd} {l=ts} prf
                                                prf_emp = all_true_empties_filter prf_all
                                            in  rewrite prf_emp in (Refl, Refl)
fail_no_inter (Edit n (Change _))  s Refl impossible
fail_no_inter (Edit n (Watch _))   s Refl impossible
fail_no_inter (Pair t1 t2)         s p_f12 with (failing t1 ?= True, failing t2 ?= True)
  fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, Yes p_f2) with (fail_no_inter t1 s p_f1, fail_no_inter t2 s p_f2)
    fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, Yes p_f2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in
                                                                                                       --> `rewrite p_v2` is not needed because of definiiton of `<&>`
                                                                                                       rewrite p_i1 in
                                                                                                       rewrite p_i2 in (Refl, Refl)
  fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) with (failing t2)
    fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | True = absurd (no_f2 Refl)
    fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False with (failing t1)
      fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False | True = absurd p_f12
      fail_no_inter (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False | False = absurd p_f12
  fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) with (failing t1)
    fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | True = absurd (no_f1 Refl)
    fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False with (failing t2)
      fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False | True = absurd p_f12
      fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False | False = absurd p_f12
  fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) with (failing t1)
    fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) | True = absurd (no_f1 Refl)
    fail_no_inter (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) | False = absurd p_f12
fail_no_inter (Done v)             s Refl impossible
fail_no_inter (Choose t1 t2)       s prf with (and_split failing t1 t2 prf)
  fail_no_inter (Choose t1 t2)       s prf | (prf_1, prf_2) with (fail_no_inter t1 s prf_1, fail_no_inter t2 s prf_2)
    fail_no_inter (Choose t1 t2)       s prf | (prf_1, prf_2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in
                                                                                               rewrite p_v2 in
                                                                                               rewrite p_i1 in
                                                                                               rewrite p_i2 in (Refl, Refl)
fail_no_inter Fail                 s Refl = (Refl, Refl)
fail_no_inter (Trans f t2)         s prf with (fail_no_inter t2 s prf)
  fail_no_inter (Trans f t2)         s prf | (p_v2, p_i2) = (rewrite p_v2 in Refl, p_i2)
fail_no_inter (Step t1 c)          s prf with (fail_no_inter t1 s prf)
  fail_no_inter (Step t1 c)          s prf | (p_v1, p_i1) = (Refl, rewrite p_i1 in rewrite p_v1 in Refl)
fail_no_inter (Assert y)           s Refl impossible
fail_no_inter (Assign v r)         s Refl impossible
