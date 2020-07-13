module Helpers

import public Decidable.Equality
import Data.Either

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
infixr 6 <>
infixr 6 <->

public export
(/\) : Type -> Type -> Type
(/\) = Pair

public export
(\/) : Type -> Type -> Type
(\/) = Either

public export
(<>) : Type -> Type -> Type
(<>) a b = (a /\ Not b) \/ (Not a /\ b)

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

public export
Uninhabited (Left e = Right x) where
  uninhabited Refl impossible

public export
Uninhabited (Right x = Left e) where
  uninhabited Refl impossible

---- IsItRight or IsItLeft -----------------------------------------------------

public export
data IsRight : Either e a -> Type where
  ItIsRight : IsRight (Right x)

public export
Uninhabited (IsRight (Left e)) where
  uninhabited ItIsRight impossible
