module Task.Proofs.Lemmas

import Helpers
import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Task.Observations

---- On evidence ---------------------------------------------------------------

||| Having both a proof that `p` and that `Not p` is not possible.
not_both_true_and_false : Not (p, Not p) -- : (p, p -> Void) -> Void
not_both_true_and_false (p, not_p) = not_p p

public export
notOrIsAndNot : Not (a \/ b) -> (Not a /\ Not b)
notOrIsAndNot f = (\x => f (Left x), \x => f (Right x))

public export
andNotIsNotOr : (Not a /\ Not b) -> Not (a \/ b)
andNotIsNotOr (f, g) (Left x)  = f x
andNotIsNotOr (f, g) (Right y) = g y

notAndIsOr : Not (a /\ b) -> (Not a \/ Not b)
notAndIsOr f = Left (\x => ?notAndIsOr_rhs)

---- On booleans ---------------------------------------------------------------

||| Having a proof that `p x && p x = True` implies a proof that `p x = True /\ p y = True`.
||| I.e. this hoists one proof on boolean-and to two type level proofs.
export
and_split : (p : a -> Bool) -> (x : a) -> (y : a) -> (p x && p y = True) -> (p x = True) /\ (p y = True)
and_split p x y prf with (p x ?= True, p y ?= True)
  and_split p x y prf | (Yes prf_x, Yes prf_y) = (prf_x, prf_y)
  and_split p x y prf | (Yes prf_x, No  not_y) with (p y)
    and_split p x y prf | (Yes prf_x, No  not_y) | True = absurd (not_y Refl)
    -- and_split p x y prf | (Yes prf_x, No  not_y) | False = rewrite prf_x in ?h...
    and_split p x y prf | (Yes prf_x, No  not_y) | False with (p x)
      and_split p x y prf | (Yes prf_x, No  not_y) | False | True  = absurd prf
      and_split p x y prf | (Yes prf_x, No  not_y) | False | False = absurd prf
  and_split p x y prf | (No  not_x, Yes prf_y) with (p x)
    and_split p x y prf | (No  not_x, Yes prf_y) | True = absurd (not_x Refl)
    and_split p x y prf | (No  not_x, Yes prf_y) | False with (p y)
      and_split p x y prf | (No  not_x, Yes prf_y) | False | True  = absurd prf
      and_split p x y prf | (No  not_x, Yes prf_y) | False | False = absurd prf
  and_split p x y prf | (No  not_x, No  not_y) with (p x)
    and_split p x y prf | (No  not_x, No  not_y) | True = absurd (not_x Refl)
    and_split p x y prf | (No  not_x, No  not_y) | False = absurd prf

export
and_merge : {p : a -> Bool} -> (p x = True) /\ (p y = True) -> (p x && p y = True)
and_merge {p} (p_x, p_y) = rewrite p_x in rewrite p_y in Refl

export
and_merge_inh : {p1 : a -> Bool} -> {p2 : b -> Bool} -> (p1 x = True) /\ (p2 y = True) -> (p1 x && p2 y = True)
and_merge_inh (p_x, p_y) = rewrite p_x in rewrite p_y in Refl

---- On maybes -----------------------------------------------------------------

export
notJustIsNothing : {x : Maybe a} -> Not (IsJust x) -> (x = Nothing)
notJustIsNothing {x = Nothing}  _ = Refl
notJustIsNothing {x = (Just _)} f = void (f ItIsJust)

export
mapIsJust : {f : a -> b} -> IsJust (map f x) -> IsJust x
mapIsJust prf = ?mapIsJust_rhs
-- mapIsJust = ?mapIsJust_rhs
-- mapIsJust ItIsJust = ItIsJust

export
map_over_nothing_is_nothing : {x : Maybe a} -> (map f x = Nothing) -> (x = Nothing)
map_over_nothing_is_nothing {x = Nothing} _    = Refl
map_over_nothing_is_nothing {x = (Just x)} prf = absurd prf

export
choose_results_nothing : {x : Maybe a} -> {y : Maybe a} -> (x <|> y = Nothing) -> (x = Nothing) /\ (y = Nothing)
choose_results_nothing {x = Nothing} {y = Nothing} prf = (Refl, Refl)
choose_results_nothing {x = Nothing} {y = Just _ } prf = absurd prf
choose_results_nothing {x = Just _ } {y = Nothing} prf = absurd prf
choose_results_nothing {x = Just _ } {y = Just _ } prf = absurd prf

export
pair_results_nothing : {x : Maybe a} -> {y : Maybe b} -> (x <&> y = Nothing) -> (x = Nothing) \/ (y = Nothing)
pair_results_nothing {x = Nothing} {y = Nothing} prf = Left Refl
pair_results_nothing {x = Nothing} {y = Just _ } prf = Left Refl
pair_results_nothing {x = Just _ } {y = Nothing} prf = Right Refl
pair_results_nothing {x = Just _ } {y = Just _ } prf = Left (absurd prf)

---- On lists ------------------------------------------------------------------

export
notNonEmptyIsNil: {l : List a} -> Not (NonEmpty l) -> (l = [])
notNonEmptyIsNil {l = []}      f = Refl
notNonEmptyIsNil {l = x :: xs} f = void (f IsNonEmpty)

---- All

||| Folding on `&&` with a start accumulator of `False` won't give us a `True` result.
not_foldl_and_false : {p : a -> Bool} -> (l : List a) -> Not (foldl (\x,y => x && p y) False l = True)
not_foldl_and_false [] Refl impossible
not_foldl_and_false (x :: xs) prf = let rec = not_foldl_and_false xs in not_both_true_and_false (prf, rec)

||| If we have that `all p l = True` for any list `l` and predicate `p`,
||| we know `p` holds for the head and for the fold over the tail of the l.
all_split_head_and_tail : {p : a -> Bool} -> (l : List a) -> {auto ok : NonEmpty l} -> (all p l = True) -> (p (head l) = True) /\ (all p (tail l) = True)
all_split_head_and_tail [] _ impossible
all_split_head_and_tail (x :: xs) prf with (p x)
  all_split_head_and_tail (x :: xs) prf | True with (all p xs)
    all_split_head_and_tail (x :: xs) prf | True | True = (Refl, Refl)
    all_split_head_and_tail (x :: xs) prf | True | False = absurd (prf)
  all_split_head_and_tail (x :: xs) prf | False = absurd (not_foldl_and_false xs prf)

||| Hoists a predicate of `all` to evindence of `All`.
export
hoist_all : {p : a -> Bool} -> {l : List a} -> (all p l = True) -> All (\x => p x = True) l
hoist_all {l = []} prf = []
hoist_all {l = (x :: xs)} prf with (all_split_head_and_tail (x :: xs) prf)
  hoist_all {l = (x :: xs)} prf | (prf_x, prf_xs) = prf_x :: hoist_all prf_xs

||| Lowers evindence of `All` to a predicate of `all`.
export
lower_all : All (\x => p x = True) xs -> (all p xs = True)
lower_all [] = Refl
lower_all (yes_x :: yes_xs) = rewrite yes_x in lower_all yes_xs

||| When we have evidence that predicate `p` holds for every `x` in list `l`,
||| filtering `l` on `not . p` results in an empty list.
export
all_true_empties_filter : {p : a -> Bool} -> {l : List a} -> All (\x => p x = True) l -> (filter (\x => not (p x)) l = [])
all_true_empties_filter {l = []} _ = Refl
all_true_empties_filter {l = (x :: xs)} (prf :: prfs) = rewrite prf in all_true_empties_filter prfs

---- Append

||| When the append of two lists is empty, both has to be empty themselves.
export
append_results_empties : {l1 : List a} -> {l2 : List a} -> (l1 ++ l2 = []) -> (l1 = []) /\ (l2 = [])
append_results_empties {l1 = []}        {l2 = []}        prf = (Refl, Refl)
append_results_empties {l1 = []}        {l2 = (y :: ys)} prf = absurd prf
append_results_empties {l1 = (x :: xs)} {l2 = []}        prf = absurd prf
append_results_empties {l1 = (x :: xs)} {l2 = (y :: ys)} prf = absurd prf
