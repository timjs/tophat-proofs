module Data.Basic

import Helpers

%default total

---- Data ----------------------------------------------------------------------

public export
data IsBasic : Type -> Type where
  BoolIsBasic   : IsBasic Bool
  IntIsBasic    : IsBasic Int
  StringIsBasic : IsBasic String
  UnitIsBasic   : IsBasic ()
  PairIsBasic   : IsBasic a -> IsBasic b -> IsBasic (a, b)

---- Lemmas --------------------------------------------------------------------

uninhBoolInt : Not (BoolIsBasic = IntIsBasic)
uninhBoolInt Refl impossible

uninhBoolString : Not (BoolIsBasic = StringIsBasic)
uninhBoolString Refl impossible

uninhBoolUnit : Not (BoolIsBasic = UnitIsBasic)
uninhBoolUnit Refl impossible

uninhBoolPair : Not (BoolIsBasic = PairIsBasic _ _)
uninhBoolPair Refl impossible

uninhIntString : Not (IntIsBasic = StringIsBasic)
uninhIntString Refl impossible

uninhIntUnit : Not (IntIsBasic = UnitIsBasic)
uninhIntUnit Refl impossible

uninhIntPair : Not (IntIsBasic = PairIsBasic _ _)
uninhIntPair Refl impossible

uninhStringUnit : Not (StringIsBasic = UnitIsBasic)
uninhStringUnit Refl impossible

uninhStringPair : Not (StringIsBasic = PairIsBasic _ _)
uninhStringPair Refl impossible

uninhUnitPair : Not (UnitIsBasic = PairIsBasic _ _)
uninhUnitPair Refl impossible

basicInjective : (IsBasic a = IsBasic b) -> (a = b)
basicInjective Refl = Refl

symBasic : {0 p : IsBasic a} -> {0 q : IsBasic b} -> (p = q) -> (q = p)
symBasic Refl = Refl

negEqSymBasic : {0 p : IsBasic a} -> {0 q : IsBasic b} -> Not (p = q) -> Not (q = p)
negEqSymBasic f prf = f (symBasic prf)

fstNeq : {0 p : IsBasic a} -> {0 q : IsBasic b} -> Not (x1 = x') -> Not (PairIsBasic x1 y2 = PairIsBasic x' y2)
fstNeq cntr Refl = cntr Refl

sndNeq : {0 p : IsBasic a} -> {0 q : IsBasic b} -> Not (y1 = y') -> Not (PairIsBasic x1 y1 = PairIsBasic x1 y')
sndNeq cntr Refl = cntr Refl

bothNeq : {0 p : IsBasic a} -> {0 q : IsBasic b} -> Not (x1 = x') -> Not (y1 = y') -> Not (PairIsBasic x1 y1 = PairIsBasic x' y')
bothNeq cntr_a cntr_b Refl = cntr_a Refl

---- Equality ------------------------------------------------------------------

infix 6 ?:

public export
decBasic : (b1 : IsBasic a1) -> (b2 : IsBasic a2) -> Dec (b1 = b2)
decBasic BoolIsBasic         BoolIsBasic         = Yes Refl
decBasic BoolIsBasic         IntIsBasic          = No uninhBoolInt
decBasic BoolIsBasic         StringIsBasic       = No uninhBoolString
decBasic BoolIsBasic         UnitIsBasic         = No uninhBoolUnit
decBasic BoolIsBasic         (PairIsBasic x2 y2) = No uninhBoolPair
decBasic IntIsBasic          BoolIsBasic         = No (negEqSymBasic uninhBoolInt)
decBasic IntIsBasic          IntIsBasic          = Yes Refl
decBasic IntIsBasic          StringIsBasic       = No uninhIntString
decBasic IntIsBasic          UnitIsBasic         = No uninhIntUnit
decBasic IntIsBasic          (PairIsBasic x2 y2) = No uninhIntPair
decBasic StringIsBasic       BoolIsBasic         = No (negEqSymBasic uninhBoolString)
decBasic StringIsBasic       IntIsBasic          = No (negEqSymBasic uninhIntString)
decBasic StringIsBasic       StringIsBasic       = Yes Refl
decBasic StringIsBasic       UnitIsBasic         = No uninhStringUnit
decBasic StringIsBasic       (PairIsBasic x2 y2) = No uninhStringPair
decBasic UnitIsBasic         BoolIsBasic         = No (negEqSymBasic uninhBoolUnit)
decBasic UnitIsBasic         IntIsBasic          = No (negEqSymBasic uninhIntUnit)
decBasic UnitIsBasic         StringIsBasic       = No (negEqSymBasic uninhStringUnit)
decBasic UnitIsBasic         UnitIsBasic         = Yes Refl
decBasic UnitIsBasic         (PairIsBasic x1 y2) = No uninhUnitPair
decBasic (PairIsBasic x1 y1) BoolIsBasic         = No (negEqSymBasic uninhBoolPair)
decBasic (PairIsBasic x1 y1) IntIsBasic          = No (negEqSymBasic uninhIntPair)
decBasic (PairIsBasic x1 y1) StringIsBasic       = No (negEqSymBasic uninhStringPair)
decBasic (PairIsBasic x1 y1) UnitIsBasic         = No (negEqSymBasic uninhUnitPair)
decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y2) with (decBasic x1 x2, decBasic y1 y2)
  decBasic (PairIsBasic x1 y1) (PairIsBasic x1 y1) | (Yes Refl, Yes Refl) = Yes Refl
  decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y1) | (No cntr1, Yes Refl) = No ?decBasicPairNopYes
  decBasic (PairIsBasic x1 y1) (PairIsBasic x1 y2) | (Yes Refl, No cntr2) = No ?decBasicPairYesNop
  decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y2) | (No cntrq, No cntr2) = No ?decBasicPairNopNop

export
neqBasic : Not (IsBasic a = IsBasic b) -> Not (a = b)
neqBasic f Refl = f Refl

export
(?:) : a -> {auto p : IsBasic a} -> b -> {auto q : IsBasic b} -> Dec (p = q)
(?:) _ {p} _ {q} = decBasic p q

---- Existentials --------------------------------------------------------------

public export
Some : (Type -> Type) -> Type
Some f = (a : Type ** (IsBasic a, f a))

export
implementation Eq1 f => Eq (Some f) where
  (==) (a1 ** (b1, v1)) (a2 ** (b2, v2)) with (decBasic b1 b2) --(a1 ?: a2)
    (==) (Bool   ** (BoolIsBasic  , v1)) (Bool   ** (BoolIsBasic  , v2)) | Yes Refl = eq1 v1 v2
    -- (==) (Int    ** (IntIsBasic   , v1)) (Int    ** (IntIsBasic   , v2)) | Yes Refl = eq1 v1 v2
    -- (==) (Int ** (IntIsBasic, v1)) (Int ** (IntIsBasic, v2)) | Yes Refl = eq1 v1 v2
    -- (==) (()     ** (UnitIsBasic  , v1)) (()     ** (UnitIsBasic  , v2)) | Yes Refl = eq1 v1 v2
    (==) (a1     ** (b1           , v1)) (a1     ** (b1           , v2)) | Yes Refl = ?eq_some_f_same_a
    (==) (a1 ** (b1, v1)) (a2 ** (b2, e2)) | No contr = False