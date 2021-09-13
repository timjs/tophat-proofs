module Task.Proofs.Static

import Helpers
import Data.Maybe
import Data.List
import Data.List.Quantifiers
import Task.Syntax
import Task.Observe
import Task.Run
import Task.Proofs.Lemmas

%default total

---- Lemmas --------------------------------------------------------------------

map_IsJust : IsJust x -> IsJust (map f x)
map_IsJust ItIsJust = ItIsJust

pair_IsJust : IsJust x -> IsJust y -> IsJust (x <&> y)
pair_IsJust ItIsJust ItIsJust = ItIsJust

alt_IsNothing : IsNothing x -> IsNothing y -> IsNothing (x <|> y)
alt_IsNothing Refl Refl = Refl

unmap_IsJust : {x : Maybe a} -> IsJust (map f x) -> IsJust x
unmap_IsJust {x=Just v} ItIsJust = ItIsJust

unpair_IsJust : {x : Maybe a} -> {y : Maybe b} -> IsJust (x <&> y) -> IsJust x /\ IsJust y
unpair_IsJust {x=Just v} {y=Just w} ItIsJust = (ItIsJust, ItIsJust)

unalt_IsJust : {x : Maybe a} -> {y : Maybe a} -> IsJust (x <|> y) -> IsJust x \/ IsJust y
unalt_IsJust {x=Just v}  {y=_}       ItIsJust = Left ItIsJust
unalt_IsJust {x=Nothing} {y=Just w } ItIsJust = Right ItIsJust

||| Axiom, not provable in this system, would need to rewrite Task.Run.normalise using decidability on value observation, because now we'd need to "reverse engineer" the normalisation algorithm...
normal_choose_means_no_value : (t : Task h b) -> IsNormal t => {t1 : Task h b} -> IsNormal t1 => {t2 : Task h b} -> IsNormal t2 => (s : Heap h) -> (t = Choose t1 t2) -> IsNothing (value t1 s) /\ IsNothing (value t2 s)
-- normal_choose_means_no_value (Choose t1 t2) s Refl with (normalise (Choose t1 t2) (wrap s))
--   normal_choose_means_no_value (Choose t1 t2) s Refl | ((t' ** n'), s', d') with (value t1 s, value t2 s)
--     normal_choose_means_no_value (Choose t1 t2) s Refl | ((t' ** n'), s', d') | (v1, v2) = (believe_me Refl, believe_me Refl)


---- Propositions --------------------------------------------------------------

static_means_normal : (t : Task h b) -> IsStatic t => IsNormal t
static_means_normal (Edit (Named k) (Update v)) @{UpdateIsStatic}     = EditIsNormal
static_means_normal (Edit (Named k) (View v))   @{ViewIsStatic}       = EditIsNormal
static_means_normal (Edit (Named k) (Change v)) @{ChangeIsStatic}     = EditIsNormal
static_means_normal (Edit (Named k) (Watch v))  @{WatchIsStatic}      = EditIsNormal
static_means_normal (Pair t1 t2)                @{PairIsStatic s1 s2} = PairIsNormal (static_means_normal t1) (static_means_normal t2)
static_means_normal (Done v)                    @{DoneIsStatic}       = DoneIsNormal
static_means_normal (Trans e1 t2)               @{TransIsStatic s1}   = TransIsNormal (static_means_normal t2)

static_means_valued : (t : Task h b) -> IsStatic t => (s : Heap h) -> IsJust (value t @{static_means_normal t} s)
static_means_valued (Edit (Named k) (Update v)) @{UpdateIsStatic}     s = ItIsJust
static_means_valued (Edit (Named k) (View v))   @{ViewIsStatic}       s = ItIsJust
static_means_valued (Edit (Named k) (Change v)) @{ChangeIsStatic}     s = ItIsJust
static_means_valued (Edit (Named k) (Watch v))  @{WatchIsStatic}      s = ItIsJust
static_means_valued (Pair t1 t2)                @{PairIsStatic s1 s2} s with (static_means_valued t1 s, static_means_valued t2 s)
  static_means_valued (Pair t1 t2)                @{PairIsStatic s1 s2} s | (prf1, prf2) = pair_IsJust prf1 prf2
static_means_valued (Done v)                    @{DoneIsStatic}       s = ItIsJust
static_means_valued (Trans e1 t2)               @{TransIsStatic s1}   s with (static_means_valued t2 s)
  static_means_valued (Trans e1 t2)               @{TransIsStatic s1}   s | prf = map_IsJust prf

valued_means_static : (t : Task h b) -> IsNormal t => (s : Heap h) -> IsJust (value t s) -> IsStatic t
valued_means_static (Edit (Named k) (Enter))    @{EditIsNormal}         s ItIsJust impossible
valued_means_static (Edit (Named k) (Update v)) @{EditIsNormal}         s ItIsJust = UpdateIsStatic
valued_means_static (Edit (Named k) (View v))   @{EditIsNormal}         s ItIsJust = ViewIsStatic
valued_means_static (Edit (Named k) (Change v)) @{EditIsNormal}         s ItIsJust = ChangeIsStatic
valued_means_static (Edit (Named k) (Watch v))  @{EditIsNormal}         s ItIsJust = WatchIsStatic
valued_means_static (Pair t1 t2)                @{PairIsNormal n1 n2}   s prf with (unpair_IsJust prf)
  valued_means_static (Pair t1 t2)                @{PairIsNormal n1 n2}   s prf | (prf1, prf2) with (valued_means_static t1 s prf1, valued_means_static t2 s prf2)
  valued_means_static (Pair t1 t2)                @{PairIsNormal n1 n2}   s prf | (prf1, prf2) | (s1, s2) = PairIsStatic s1 s2
valued_means_static (Done v)                    @{DoneIsNormal}         s ItIsJust = DoneIsStatic
valued_means_static Fail                        @{FailIsNormal}         s ItIsJust impossible
valued_means_static (Choose t1 t2)              @{ChooseIsNormal n1 n2} s prf with (normal_choose_means_no_value (Choose t1 t2) s Refl)
  valued_means_static (Choose t1 t2)              @{ChooseIsNormal n1 n2} s prf | (cntr1, cntr2) = let cntr = alt_IsNothing cntr1 cntr2 in void (justNothingAbsurd (prf, cntr))
valued_means_static (Trans e1 t2)               @{TransIsNormal n2}     s prf with (valued_means_static t2 s (unmap_IsJust prf))
  valued_means_static (Trans e1 t2)               @{TransIsNormal n2}     s prf | s1 = TransIsStatic s1
valued_means_static (Step t1 e2)                @{StepIsNormal n1}      s ItIsJust impossible

interact' : (t : Task h a) -> IsNormal t => Input Concrete -> State h -> (Refined (Task h a) IsNormal, State h)

static_stays_static : (t : Task h b) -> IsStatic t => (i : Input Concrete) -> (s : State h) -> {t' : Task h b} -> (interact' t @{static_means_normal t} i s = (t', s')) -> IsStatic t'