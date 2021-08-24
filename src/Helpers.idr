module Helpers

import public Decidable.Equality
import public Control.Monoidal
-- import public Data.Bool
import public Data.Either
import public Data.Fin
import public Data.List
import public Data.Maybe
import public Data.Vect

%default total

---- Decidability --------------------------------------------------------------

infix 6 ?=

||| Although in Idris it is not common to use loads of operators,
||| having one for `decEq` looks better on the eyes.
public export
(?=) : DecEq t => (x : t) -> (y : t) -> Dec (x = y)
(?=) = decEq

---- Refinements ---------------------------------------------------------------

public export
-- data Refined : (a : Type) -> (a -> Type) -> Type where
--   Refine : (x : a) -> p x -> Refined a p
Refined : (a : Type) -> (a -> Type) -> Type
Refined = DPair

public export
refine : (x : a) -> {auto c : p x} -> Refined a p
refine x {c} = (x ** c)

public export
unrefine : Refined a p -> a
unrefine (x ** _) = x

public export
implicate : (Refined a f -> b) -> ((x : a) -> f x => b)
implicate g x = g (refine x)

public export
unimplicate : ((x : a) -> f x => b) -> (Refined a f -> b)
unimplicate g (x ** p) = g x

---- Equality of type constructors ---------------------------------------------

public export
interface Eq1 f where
  -- (===) : Eq a => f a -> f a -> Bool
  eq1 : Eq a => f a -> f a -> Bool

-- infix 4 ===

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
-- (<>) a b = Not a <-> b

public export
(<->) : Type -> Type -> Type
(<->) a b = (a -> b, b -> a)

public export
iff : (a <-> b) -> (b <-> a)
iff (p_a, p_b) = (p_b, p_a)

---- Habited or Unhabited ------------------------------------------------------
--FIXME: here because not yet in Data.Bool and Data.Maybe in 0.2.0...

-- public export
-- Uninhabited (True = False) where
--   uninhabited Refl impossible

-- public export
-- Uninhabited (False = True) where
--   uninhabited Refl impossible

-- public export
-- Uninhabited (Just x = Nothing) where
--   uninhabited Refl impossible

-- public export
-- Uninhabited (Nothing = Just y) where
--   uninhabited Refl impossible

-- public export
-- Uninhabited (Left e = Right x) where
--   uninhabited Refl impossible

-- public export
-- Uninhabited (Right x = Left e) where
--   uninhabited Refl impossible

export
notTrueIsFalse : {1 b : Bool} -> Not (b = True) -> b = False
notTrueIsFalse {b = True}  nope = absurd (nope Refl)
notTrueIsFalse {b = False} nope = Refl

export
notFalseIsTrue : {1 b : Bool} -> Not (b = False) -> b = True
notFalseIsTrue {b = True}  nope = Refl
notFalseIsTrue {b = False} nope = absurd (nope Refl)

---- Operators -----------------------------------------------------------------

infixr 0 ~>
infixl 1 |>
infixr 9 .>

public export
(~>) : a -> b -> (a, b)
(~>) x y = (x, y)

public export
(|>) : a -> (a -> b) -> b
(|>) x f = f x

public export
(.>) : (a -> b) -> (b -> c) -> (a -> c)
(.>) f g x = g (f x)

---- Vectors -------------------------------------------------------------------

public export
foldi : (Nat -> b -> a -> b) -> b -> List a -> b
foldi = foldi' Z
where
  foldi' : Nat -> (Nat -> b -> a -> b) -> b -> List a -> b
  foldi' i g a [] = a
  foldi' i g a (x :: xs) = foldi' (S i) g (g i a x) xs

---- Fins ----------------------------------------------------------------------

export
Show (Fin _) where
  show = show . finToNat

---- Monads --------------------------------------------------------------------

public export
done : Monad m => a -> m a
done = pure

---- IsItTrue or IsItFalse -----------------------------------------------------

public export
IsTrue : Bool -> Type
IsTrue x = x = True

public export
isItTrue : (1 b : Bool) -> Dec (IsTrue b)
isItTrue True  = Yes Refl
isItTrue False = No absurd

public export
IsFalse : Bool -> Type
IsFalse x = x = False

public export
isItFalse : (1 b : Bool) -> Dec (IsFalse b)
isItFalse True  = No absurd
isItFalse False = Yes Refl

---- IsItJust or IsItNothing ---------------------------------------------------

-- IsJust    NotJust
-- IsTrue    NotTrue
-- IsRight   NotRight
-- IsCons    NotCons
-- IsNil     NotNil
-- IsEmpty   NonEmpty
-- HasElems  HasntElems
-- IsntEmpty IsEmpty
-- NonEmpty  Empty

public export
IsNothing : Maybe a -> Type
IsNothing x = x = Nothing

public export
isItNothing : (m : Maybe a) -> Dec (IsNothing m)
isItNothing (Nothing) = Yes Refl
isItNothing (Just _)  = No absurd

export
notJustIsNothing : {m : Maybe a} -> Not (IsJust m) -> IsNothing m
notJustIsNothing {m = Nothing} _ = Refl
notJustIsNothing {m = Just _}  f = void (f ItIsJust)

export
notNothingIsJust : {m : Maybe a} -> Not (IsNothing m) -> IsJust m
notNothingIsJust {m = Nothing} f = void (f Refl)
notNothingIsJust {m = Just _}  f = ItIsJust

---- IsItRight or IsItLeft -----------------------------------------------------

public export
data IsRight : Either e a -> Type where
  ItIsRight : IsRight (Right x)

public export
Uninhabited (IsRight (Left e)) where
  uninhabited ItIsRight impossible

public export
isItRight : (v : Either e a) -> Dec (IsRight v)
isItRight (Right _) = Yes ItIsRight
isItRight (Left  _) = No absurd

public export
data IsLeft : Either e a -> Type where
  ItIsLeft : IsLeft (Left x)

public export
Uninhabited (IsLeft (Right e)) where
  uninhabited ItIsLeft impossible

public export
isItLeft : (v : Either e a) -> Dec (IsLeft v)
isItLeft (Left  _) = Yes ItIsLeft
isItLeft (Right _) = No absurd

public export
notRightIsLeft : {v : Either e a} -> Not (IsRight v) -> IsLeft v
notRightIsLeft {v=Left  x} cntr = ItIsLeft
notRightIsLeft {v=Right x} cntr = void (cntr ItIsRight)

public export
notLeftIsRight : {v : Either e a} -> Not (IsLeft v) -> IsRight v
notLeftIsRight {v=Left  x} cntr = void (cntr ItIsLeft)
notLeftIsRight {v=Right x} cntr = ItIsRight

---- IsItNil or IsItCons -------------------------------------------------------

public export
IsNil : List a -> Type
IsNil xs = xs = []

public export
isItNil : (l : List a) -> Dec (IsNil l)
isItNil []       = Yes Refl
isItNil (_ :: _) = No absurd

public export
IsCons : List a -> Type
IsCons = NonEmpty

public export
ItIsCons : IsCons (x :: xs)
ItIsCons = IsNonEmpty

-- public export
-- data IsCons : List a -> Type where
--   ItIsCons : IsCons (x :: xs)

-- public export
-- Uninhabited (IsCons []) where
--   uninhabited ItIsCons impossible

public export
isItCons : (l : List a) -> Dec (IsCons l)
isItCons []       = No absurd
isItCons (_ :: _) = Yes ItIsCons

export
notConsIsNil: {l : List a} -> Not (IsCons l) -> IsNil l
notConsIsNil {l = []}     nope = Refl
notConsIsNil {l = _ :: _} nope = void (nope ItIsCons)
