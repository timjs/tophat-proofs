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

export
failingMeansNoInteraction : (t : Task h b) -> (s : State h) -> IsTrue (failing t) -> IsNothing (value t s) /\ IsNil (inputs t s)
failingMeansNoInteraction (Edit n (Enter))     s Refl impossible
failingMeansNoInteraction (Edit n (Update _))  s Refl impossible
failingMeansNoInteraction (Edit n (View _))    s Refl impossible
failingMeansNoInteraction (Edit n (Select ts)) s prf  = let prf_all = hoist_all {p=failing . snd} {l=ts} prf
                                                            prf_emp = all_true_empties_filter prf_all
                                                        in  rewrite prf_emp in (Refl, Refl)
failingMeansNoInteraction (Edit n (Change _))  s Refl impossible
failingMeansNoInteraction (Edit n (Watch _))   s Refl impossible
failingMeansNoInteraction (Pair t1 t2)         s p_f12 with (failing t1 ?= True, failing t2 ?= True)
  failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, Yes p_f2) with (failingMeansNoInteraction t1 s p_f1, failingMeansNoInteraction t2 s p_f2)
    --> `rewrite p_v2` is not needed because of definiiton of `<&>`
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, Yes p_f2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in rewrite p_i1 in rewrite p_i2 in (Refl, Refl)
  failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) with (failing t2)
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | True = absurd (no_f2 Refl)
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False with (failing t1)
      failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False | True = absurd p_f12
      failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (Yes p_f1, No no_f2) | False | False = absurd p_f12
  failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) with (failing t1)
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | True = absurd (no_f1 Refl)
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False with (failing t2)
      failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False | True = absurd p_f12
      failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, Yes p_f2) | False | False = absurd p_f12
  failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) with (failing t1)
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) | True = absurd (no_f1 Refl)
    failingMeansNoInteraction (Pair t1 t2)         s p_f12 | (No no_f1, No no_f2) | False = absurd p_f12
failingMeansNoInteraction (Done v)             s Refl impossible
failingMeansNoInteraction (Choose t1 t2)       s prf with (and_split failing t1 t2 prf)
  failingMeansNoInteraction (Choose t1 t2)       s prf | (prf_1, prf_2) with (failingMeansNoInteraction t1 s prf_1, failingMeansNoInteraction t2 s prf_2)
    failingMeansNoInteraction (Choose t1 t2)       s prf | (prf_1, prf_2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in rewrite p_v2 in rewrite p_i1 in rewrite p_i2 in (Refl, Refl)
failingMeansNoInteraction Fail                 s Refl = (Refl, Refl)
failingMeansNoInteraction (Trans f t2)         s prf with (failingMeansNoInteraction t2 s prf)
  failingMeansNoInteraction (Trans f t2)         s prf | (p_v2, p_i2) = (rewrite p_v2 in Refl, p_i2)
failingMeansNoInteraction (Step t1 c)          s prf with (failingMeansNoInteraction t1 s prf)
  failingMeansNoInteraction (Step t1 c)          s prf | (p_v1, p_i1) = (Refl, rewrite p_i1 in rewrite p_v1 in Refl)
failingMeansNoInteraction (Assert y)           s Refl impossible
failingMeansNoInteraction (Assign v r)         s Refl impossible
