module Helpers

import public Decidable.Equality

%default total

---- Decidability --------------------------------------------------------------

infix 6 ?=

||| Although in Idris it is not common to use loads of operators,
||| having one for `decEq` looks better on the eyes.
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

---- Habited or Unhabited ------------------------------------------------------
--FIXME: here because not yet in Data.Bool and Data.Maybe in 0.2.0...

public export
Uninhabited (True = False) where
  uninhabited Refl impossible

public export
Uninhabited (False = True) where
  uninhabited Refl impossible

public export
Uninhabited (Just x = Nothing) where
  uninhabited Refl impossible

public export
Uninhabited (Nothing = Just y) where
  uninhabited Refl impossible
