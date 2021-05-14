module Task.Proofs.Failing

import Helpers
import Data.Maybe
import Data.List
import Data.List.Quantifiers
import Task.Syntax
import Task.Observe
import Task.Proofs.Lemmas

%default total

---- Interaction ---------------------------------------------------------------

export
failingMeansNoInteraction : (t : Task h b) -> IsNormal t => (s : Heap h) -> IsTrue (failing t) -> IsNothing (value t s) /\ IsNil (inputs t s)
failingMeansNoInteraction (Pair t1 t2)                 @{PairIsNormal n1 n2}   s is_f12 with (failing t1 ?= True, failing t2 ?= True)
  failingMeansNoInteraction (Pair t1 t2)               @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, Yes is_f2) with (failingMeansNoInteraction t1 s is_f1, failingMeansNoInteraction t2 s is_f2)
    --> `rewrite is_v2` is not needed because of definiiton of `<&>`
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, Yes is_f2) | ((is_v1, is_i1), (is_v2, is_i2)) = rewrite is_v1 in rewrite is_i1 in rewrite is_i2 in (Refl, Refl)
  failingMeansNoInteraction (Pair t1 t2)               @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, No not_f2) with (failing t2)
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, No not_f2) | True = absurd (not_f2 Refl)
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, No not_f2) | False with (failing t1)
      failingMeansNoInteraction (Pair t1 t2)           @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, No not_f2) | False | True = absurd is_f12
      failingMeansNoInteraction (Pair t1 t2)           @{PairIsNormal n1 n2}   s is_f12 | (Yes is_f1, No not_f2) | False | False = absurd is_f12
  failingMeansNoInteraction (Pair t1 t2)               @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, Yes is_f2) with (failing t1)
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, Yes is_f2) | True = absurd (not_f1 Refl)
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, Yes is_f2) | False with (failing t2)
      failingMeansNoInteraction (Pair t1 t2)           @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, Yes is_f2) | False | True = absurd is_f12
      failingMeansNoInteraction (Pair t1 t2)           @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, Yes is_f2) | False | False = absurd is_f12
  failingMeansNoInteraction (Pair t1 t2)               @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, No not_f2) with (failing t1)
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, No not_f2) | True = absurd (not_f1 Refl)
    failingMeansNoInteraction (Pair t1 t2)             @{PairIsNormal n1 n2}   s is_f12 | (No not_f1, No not_f2) | False = absurd is_f12
failingMeansNoInteraction (Choose t1 t2)               @{ChooseIsNormal n1 n2} s is_f with (and_split failing t1 t2 is_f)
  failingMeansNoInteraction (Choose t1 t2)             @{ChooseIsNormal n1 n2} s is_f | (is_f1, is_f2) with (failingMeansNoInteraction t1 s is_f1, failingMeansNoInteraction t2 s is_f2)
    failingMeansNoInteraction (Choose t1 t2)           @{ChooseIsNormal n1 n2} s is_f | (is_f1, is_f2) | ((is_v1, is_i1), (is_v2, is_i2)) = rewrite is_v1 in rewrite is_v2 in rewrite is_i1 in rewrite is_i2 in (Refl, Refl)
failingMeansNoInteraction (Fail)                       @{FailIsNormal}         s Refl = (Refl, Refl)
failingMeansNoInteraction (Trans f t2)                 @{TransIsNormal n2}     s is_f with (failingMeansNoInteraction t2 s is_f)
  failingMeansNoInteraction (Trans f t2)               @{TransIsNormal n2}     s is_f | (is_v2, is_i2) = (rewrite is_v2 in Refl, is_i2)
failingMeansNoInteraction (Step t1 c)                  @{StepIsNormal n1}      s is_f with (failingMeansNoInteraction t1 s is_f)
  failingMeansNoInteraction (Step t1 c)                @{StepIsNormal n1}      s is_f | (is_v1, is_i1) = (Refl, is_i1)
failingMeansNoInteraction (Select _ t1 bs)             @{SelectIsNormal n1}    s is_f with (failingMeansNoInteraction t1 s is_f)
  failingMeansNoInteraction (Select _ t1 bs)           @{SelectIsNormal n1}    s is_f | (is_v1, is_i1) = (Refl, rewrite is_v1 in rewrite is_i1 in Refl)