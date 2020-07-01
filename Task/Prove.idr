module Task.Prove

import Helpers
import Data.Maybe
import Task.Syntax
import Task.Observe

%default total


---- Interaction ---------------------------------------------------------------

no_inter_fail : (t : Task h b) -> (s : State h) -> (value t s = Nothing) /\ (inputs t s = []) -> (failing t = True)
no_inter_fail (Edit n (Enter))     s prfs = ?no_inter_fail_r_1
no_inter_fail (Edit n (Update _))  s prfs = ?no_inter_fail_r_2
no_inter_fail (Edit n (View _))    s prfs = ?no_inter_fail_r_3
no_inter_fail (Edit n (Select ts)) s prfs = ?no_inter_fail_r_4
no_inter_fail (Edit n (Change _))  s prfs = ?no_inter_fail_r_5
no_inter_fail (Edit n (Watch _))   s prfs = ?no_inter_fail_r_6
no_inter_fail (Pair t1 t2)         s prfs = ?no_inter_fail_r_7
no_inter_fail (Done v)             s prfs = ?no_inter_fail_r_8
no_inter_fail (Choose t1 t2)       s prfs = ?no_inter_fail_r_9
no_inter_fail (Fail)               s prfs = ?no_inter_fail_r_10
no_inter_fail (Trans f t)          s prfs = ?no_inter_fail_r_11
no_inter_fail (Step t c)           s prfs = ?no_inter_fail_r_12
no_inter_fail (Assert z)           s prfs = ?no_inter_fail_r_13
no_inter_fail (Assign v r)         s prfs = ?no_inter_fail_r_14

fail_no_inter : (t : Task h b) -> (s : State h) -> (failing t = True) -> (value t s = Nothing) /\ (inputs t s = [])
fail_no_inter (Edit n (Enter))     s Refl impossible
fail_no_inter (Edit n (Update _))  s Refl impossible
fail_no_inter (Edit n (View _))    s Refl impossible
fail_no_inter (Edit n (Select ts)) s prf = ?fail_no_inter_r_4_rhs
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
fail_no_inter (Choose t1 t2)       s prf with (failing t1 ?= True, failing t2 ?= True)
  fail_no_inter (Choose t1 t2)       s prf | (Yes p_f1, Yes p_f2) with (fail_no_inter t1 s p_f1, fail_no_inter t2 s p_f2)
    fail_no_inter (Choose t1 t2)       s prf | (Yes p_f1, Yes p_f2) | ((p_v1, p_i1), (p_v2, p_i2)) = rewrite p_v1 in
                                                                                                     rewrite p_v2 in
                                                                                                     rewrite p_i1 in
                                                                                                     rewrite p_i2 in (Refl, Refl)
  --> Use lemma for this part as it is the same as for `Pair`?
  fail_no_inter (Choose t1 t2)       s p_f12 | (Yes p_f1, No no_f2) with (failing t2)
    fail_no_inter (Choose t1 t2)       s p_f12 | (Yes p_f1, No no_f2) | True = absurd (no_f2 Refl)
    fail_no_inter (Choose t1 t2)       s p_f12 | (Yes p_f1, No no_f2) | False with (failing t1)
      fail_no_inter (Choose t1 t2)       s p_f12 | (Yes p_f1, No no_f2) | False | True = absurd p_f12
      fail_no_inter (Choose t1 t2)       s p_f12 | (Yes p_f1, No no_f2) | False | False = absurd p_f12
  fail_no_inter (Choose t1 t2)       s p_f12 | (No no_f1, Yes p_f2) with (failing t1)
    fail_no_inter (Choose t1 t2)       s p_f12 | (No no_f1, Yes p_f2) | True = absurd (no_f1 Refl)
    fail_no_inter (Choose t1 t2)       s p_f12 | (No no_f1, Yes p_f2) | False = absurd p_f12
  fail_no_inter (Choose t1 t2)       s p_f12 | (No no_f1, No no_f2) with (failing t1)
    fail_no_inter (Choose t1 t2)       s p_f12 | (No no_f1, No no_f2) | True = absurd (no_f1 Refl)
    fail_no_inter (Choose t1 t2)       s p_f12 | (No no_f1, No no_f2) | False = absurd p_f12
fail_no_inter Fail                 s Refl = (Refl, Refl)
fail_no_inter (Trans f t2)         s prf with (fail_no_inter t2 s prf)
  fail_no_inter (Trans f t2)         s prf | (p_v2, p_i2) = (rewrite p_v2 in Refl, p_i2)
fail_no_inter (Step t1 c)          s prf with (fail_no_inter t1 s prf)
  fail_no_inter (Step t1 c)          s prf | (p_v1, p_i1) = (Refl, rewrite p_i1 in rewrite p_v1 in Refl)
fail_no_inter (Assert y)           s Refl impossible
fail_no_inter (Assign v r)         s Refl impossible




failing_means_no_interaction : (t : Task h b) -> (s : State h) -> (failing t = True) <-> (value t s = Nothing) /\ (inputs t s = [])
failing_means_no_interaction t s = (fail_no_inter t s, no_inter_fail t s)






{-
no_inter_fail : Eq (typeOf b) => (t : Task h b) -> (s : State h) -> (So (value t s == Nothing), So (inputs t s == [])) -> So (failing t)
no_inter_fail (Edit n (Enter))     s prfs = andSo prfs
no_inter_fail (Edit n (Update _))  s prfs = andSo prfs
no_inter_fail (Edit n (View _))    s prfs = andSo prfs
no_inter_fail (Edit n (Select ts)) s prfs = ?no_inter_fail_rhs_100
no_inter_fail (Edit n (Change _))  s prfs = andSo prfs
no_inter_fail (Edit n (Watch _))   s prfs = andSo prfs
no_inter_fail (Pair t1 t2)         s prfs = ?no_inter_fail_rhs_3
no_inter_fail (Done v)             s prfs = andSo prfs
no_inter_fail (Choose t1 t2)       s prfs = ?no_inter_fail_rhs_4
no_inter_fail (Fail)               s prfs = andSo prfs
no_inter_fail (Trans f t)          s prfs = ?no_inter_fail_rhs_6
no_inter_fail (Step t c)           s prfs = ?no_inter_fail_rhs_7
no_inter_fail (Assert z)           s prfs = andSo prfs
no_inter_fail (Assign v r)         s prfs = andSo prfs

fail_no_inter : Eq (typeOf b) => IsBasic b => (t : Task h b) -> (s : State h) -> So (failing t) -> So ((value t s == Nothing) !& (inputs t s == []))
fail_no_inter (Edit n (Enter))     s prf = prf
fail_no_inter (Edit n (Update _))  s prf = prf
fail_no_inter (Edit n (View _))    s prf = prf
fail_no_inter (Edit n (Select ts)) s prf = ?fail_no_inter_rhs_100
fail_no_inter (Edit n (Change _))  s prf = prf
fail_no_inter (Edit n (Watch _))   s prf = prf
fail_no_inter (Pair t1 t2)         s prf = let
                                             (prf1, prf2) = soAnd prf
                                            --  res1 = fail_no_inter t1 s prf1
                                            --  res2 = fail_no_inter t2 s prf2
                                           in ?fail_no_inter_rhs_3
fail_no_inter (Done v)             s prf = prf
fail_no_inter (Choose t1 t2)       s prf = ?fail_no_inter_rhs_4
fail_no_inter Fail                 s prf = prf
fail_no_inter (Trans f t)          s prf = let
                                            --  prf = fail_no_inter t s prf
                                            x = 1
                                           in ?fail_no_inter_rhs_6
fail_no_inter (Step t c)           s prf = ?fail_no_inter_rhs_7
fail_no_inter (Assert y)           s prf = prf
fail_no_inter (Assign v r)         s prf = prf

-- fail_no_inter : Eq (typeOf b) => (t : Task h b) -> (s : State h) -> Dec (failing t = True) -> (Dec (value t s = Nothing), Dec (inputs t s = []))
-- fail_no_inter (Edit n (Enter))     s (Yes prf) = ?fail_no_inter_rhs_2
-- fail_no_inter (Edit n (Enter))     s (No contra) = ?fail_no_inter_rhs_3
-- fail_no_inter (Edit n (Update _))  s prf = ?fail_no_inter_rhs_12
-- fail_no_inter (Edit n (View _))    s prf = ?fail_no_inter_rhs_13
-- fail_no_inter (Edit n (Select ts)) s prf = ?fail_no_inter_rhs_100
-- fail_no_inter (Edit n (Change _))  s prf = ?fail_no_inter_rhs_14
-- fail_no_inter (Edit n (Watch _))   s prf = ?fail_no_inter_rhs_15
-- fail_no_inter (Pair t1 t2)         s prf with (failing t1, failing t2)
--   fail_no_inter (Pair t1 t2)         s prf | (True, True) = ?fail_no_inter_rhs_2_rhs_4
--   fail_no_inter (Pair t1 t2)         s prf | (True, False) = ?fail_no_inter_rhs_2_rhs_5
--   fail_no_inter (Pair t1 t2)         s prf | (False, True) = ?fail_no_inter_rhs_2_rhs_6
--   fail_no_inter (Pair t1 t2)         s prf | (False, False) = ?fail_no_inter_rhs_2_rhs_7
-- fail_no_inter (Done v)             s prf = ?fail_no_inter_rhs_16
-- fail_no_inter (Choose t1 t2)       s prf = ?fail_no_inter_rhs_4
-- fail_no_inter Fail                 s prf = ?fail_no_inter_rhs_17
-- fail_no_inter (Trans f t)          s prf = ?fail_no_inter_rhs_6
-- fail_no_inter (Step t c)           s prf = ?fail_no_inter_rhs_7
-- fail_no_inter (Assert y)           s prf = ?fail_no_inter_rhs_18
-- fail_no_inter (Assign v r)         s prf = ?fail_no_inter_rhs_19
-}