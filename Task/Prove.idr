module Task.Prove

import Decidable.Equality
import Data.Maybe
import Data.So
import Task.Syntax
import Task.Observe

%default total

andSo : (So a, So b) -> So (a && b)
andSo (Oh, Oh) = Oh

-- fail_valin : (t : Task h a) -> So (failing t) -> (value t == Nothing, inputs t == [])

no_valin_fail : Eq (typeOf b) => (p_b : IsBasic b) => (t : Task h b) -> (s : State h) -> (So (value t s == Nothing), So (inputs t s == [])) -> So (failing t)
no_valin_fail (Edit n (Enter))     s prfs = andSo prfs
no_valin_fail (Edit n (Update _))  s prfs = andSo prfs
no_valin_fail (Edit n (View _))    s prfs = andSo prfs
no_valin_fail (Edit n (Select ts)) s prfs = ?no_valin_fail_rhs_100
no_valin_fail (Edit n (Change _))  s prfs = andSo prfs
no_valin_fail (Edit n (Watch _))   s prfs = andSo prfs
no_valin_fail (Pair t1 t2)         s prfs = ?no_valin_fail_rhs_2
no_valin_fail (Done v)             s prfs = andSo prfs
no_valin_fail (Choose t1 t2)       s prfs = ?no_valin_fail_rhs_4
no_valin_fail (Fail)               s prfs = andSo prfs
no_valin_fail (Trans f t)          s prfs = ?no_valin_fail_rhs_6
no_valin_fail (Step t c)           s prfs = ?no_valin_fail_rhs_7
no_valin_fail (Assert z)           s prfs = andSo prfs
no_valin_fail (Assign v r)         s prfs = andSo prfs

{-
Idris: Type of valin_fail_rhs_10
 0 h : Heap
   b : Ty
   e : Editor h b
   n : Name
   s : State h
   prf : fst (runIdentity (runStateT (value (Edit n e)) s)) = Nothing
   p_i : Dec (fst (runIdentity (runStateT (inputs (Edit n e)) s)) = [])
   p_b : IsBasic b
-------------------------------------
valin_fail_rhs_10 : Dec (failing (Edit n e) = True)
-}