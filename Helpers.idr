module Helpers

import public Decidable.Equality
import Data.So

---- Decidability --------------------------------------------------------------

infix 6 ?=

public export
(?=) : DecEq t => (x : t) -> (y : t) -> Dec (x = y)
(?=) = decEq

---- Logic ---------------------------------------------------------------------

infixr 6 /\
infixr 6 \/
infixr 6 <->

public export
(/\) : Type -> Type -> Type
(/\) = Pair

public export
(\/) : Type -> Type -> Type
(\/) = Either

public export
(<->) : Type -> Type -> Type
(<->) a b = (a -> b, b -> a)

public export
iff_sym : (a <-> b) -> (b <-> a)
iff_sym (p_a, p_b) = (p_b, p_a)

---- Oh So True ----------------------------------------------------------------
--FIXME: here because not yet in Data.So in 0.2.0...

infixr 4 !&

(!&) : (1 b : Bool) -> Bool -> Bool
(!&) True  x = x
(!&) False x = False

andSo : (So a, So b) -> So (a !& b)
andSo (Oh, Oh) = Oh

soAnd : {a : Bool} -> So (a !& b) -> (So a, So b)
soAnd soab with (choose a)
  soAnd {a=True}  soab | Left Oh   = (Oh, soab)
  soAnd {a=True}  soab | Right prf = absurd prf
  soAnd {a=False} soab | Right prf = absurd soab
