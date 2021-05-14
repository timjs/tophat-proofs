module Type.Basic

import Helpers
import Data.Symbolic

%default total

---- Data ----------------------------------------------------------------------

public export
data IsBasic : Type -> Type where
  BoolIsBasic   : IsBasic Bool
  IntIsBasic    : IsBasic Int
  StringIsBasic : IsBasic String
  UnitIsBasic   : IsBasic ()
  SymbolIsBasic : IsBasic a -> IsBasic (Symbolic a)
  PairIsBasic   : IsBasic a -> IsBasic b -> IsBasic (a, b)

public export
BasicType : Type
BasicType = Refined Type IsBasic

---- Equality ------------------------------------------------------------------

export
Eq (IsBasic a) where
  BoolIsBasic         == BoolIsBasic         = True
  IntIsBasic          == IntIsBasic          = True
  StringIsBasic       == StringIsBasic       = True
  UnitIsBasic         == UnitIsBasic         = True
  SymbolIsBasic x1    == SymbolIsBasic x2    = x1 == x2
  PairIsBasic x1 y1   == PairIsBasic x2 y2   = x1 == x2 && y1 == y2
  BoolIsBasic         == _                   = False
  IntIsBasic          == _                   = False
  StringIsBasic       == _                   = False
  UnitIsBasic         == _                   = False
  SymbolIsBasic x     == _                   = False
  PairIsBasic x y     == _                   = False

---- Lemmas --------------------------------------------------------------------

uninhBoolInt : Not (BoolIsBasic = IntIsBasic)
uninhBoolInt Refl impossible

uninhBoolString : Not (BoolIsBasic = StringIsBasic)
uninhBoolString Refl impossible

uninhBoolUnit : Not (BoolIsBasic = UnitIsBasic)
uninhBoolUnit Refl impossible

uninhBoolSymbol : Not (BoolIsBasic = SymbolIsBasic _)
uninhBoolSymbol Refl impossible

uninhBoolPair : Not (BoolIsBasic = PairIsBasic _ _)
uninhBoolPair Refl impossible

uninhIntString : Not (IntIsBasic = StringIsBasic)
uninhIntString Refl impossible

uninhIntUnit : Not (IntIsBasic = UnitIsBasic)
uninhIntUnit Refl impossible

uninhIntSymbol : Not (IntIsBasic = SymbolIsBasic _)
uninhIntSymbol Refl impossible

uninhIntPair : Not (IntIsBasic = PairIsBasic _ _)
uninhIntPair Refl impossible

uninhStringUnit : Not (StringIsBasic = UnitIsBasic)
uninhStringUnit Refl impossible

uninhStringSymbol : Not (StringIsBasic = SymbolIsBasic _)
uninhStringSymbol Refl impossible

uninhStringPair : Not (StringIsBasic = PairIsBasic _ _)
uninhStringPair Refl impossible

uninhUnitSymbol : Not (UnitIsBasic = SymbolIsBasic _)
uninhUnitSymbol Refl impossible

uninhUnitPair : Not (UnitIsBasic = PairIsBasic _ _)
uninhUnitPair Refl impossible

uninhSymbolPair : Not (SymbolIsBasic _ = PairIsBasic _ _)
uninhSymbolPair Refl impossible

basicInjective : (IsBasic a = IsBasic b) -> (a = b)
basicInjective Refl = Refl

symBasic : {0 p : IsBasic a} -> {0 q : IsBasic b} -> (p = q) -> (q = p)
symBasic Refl = Refl

negEqSymBasic : {0 p : IsBasic a} -> {0 q : IsBasic b} -> Not (p = q) -> Not (q = p)
negEqSymBasic f prf = f (symBasic prf)

fstNeq : Not (x1 = x') -> Not (PairIsBasic x1 y2 = PairIsBasic x' y2)
fstNeq cntr Refl = cntr Refl

sndNeq : Not (y1 = y') -> Not (PairIsBasic x1 y1 = PairIsBasic x1 y')
sndNeq cntr Refl = cntr Refl

bothNeq : Not (x1 = x') -> Not (y1 = y') -> Not (PairIsBasic x1 y1 = PairIsBasic x' y')
bothNeq cntr_a cntr_b Refl = cntr_a Refl

---- Decidability --------------------------------------------------------------

export
decBasic : (b1 : IsBasic a1) -> (b2 : IsBasic a2) -> Dec (b1 = b2)
decBasic BoolIsBasic         BoolIsBasic         = Yes Refl
decBasic BoolIsBasic         IntIsBasic          = No uninhBoolInt
decBasic BoolIsBasic         StringIsBasic       = No uninhBoolString
decBasic BoolIsBasic         UnitIsBasic         = No uninhBoolUnit
decBasic BoolIsBasic         (SymbolIsBasic s2)  = No uninhBoolSymbol
decBasic BoolIsBasic         (PairIsBasic x2 y2) = No uninhBoolPair
decBasic IntIsBasic          BoolIsBasic         = No (negEqSymBasic uninhBoolInt)
decBasic IntIsBasic          IntIsBasic          = Yes Refl
decBasic IntIsBasic          StringIsBasic       = No uninhIntString
decBasic IntIsBasic          UnitIsBasic         = No uninhIntUnit
decBasic IntIsBasic          (SymbolIsBasic s2)  = No uninhIntSymbol
decBasic IntIsBasic          (PairIsBasic x2 y2) = No uninhIntPair
decBasic StringIsBasic       BoolIsBasic         = No (negEqSymBasic uninhBoolString)
decBasic StringIsBasic       IntIsBasic          = No (negEqSymBasic uninhIntString)
decBasic StringIsBasic       StringIsBasic       = Yes Refl
decBasic StringIsBasic       UnitIsBasic         = No uninhStringUnit
decBasic StringIsBasic       (SymbolIsBasic s2)  = No uninhStringSymbol
decBasic StringIsBasic       (PairIsBasic x2 y2) = No uninhStringPair
decBasic UnitIsBasic         BoolIsBasic         = No (negEqSymBasic uninhBoolUnit)
decBasic UnitIsBasic         IntIsBasic          = No (negEqSymBasic uninhIntUnit)
decBasic UnitIsBasic         StringIsBasic       = No (negEqSymBasic uninhStringUnit)
decBasic UnitIsBasic         UnitIsBasic         = Yes Refl
decBasic UnitIsBasic         (SymbolIsBasic s2)  = No uninhUnitSymbol
decBasic UnitIsBasic         (PairIsBasic x1 y2) = No uninhUnitPair
decBasic (SymbolIsBasic s1)  BoolIsBasic         = No (negEqSymBasic uninhBoolSymbol)
decBasic (SymbolIsBasic s1)  IntIsBasic          = No (negEqSymBasic uninhIntSymbol)
decBasic (SymbolIsBasic s1)  StringIsBasic       = No (negEqSymBasic uninhStringSymbol)
decBasic (SymbolIsBasic s1)  UnitIsBasic         = No (negEqSymBasic uninhUnitSymbol)
decBasic (SymbolIsBasic s1)  (SymbolIsBasic s2)  with (decBasic s1 s2)
  decBasic (SymbolIsBasic s1)  (SymbolIsBasic s1)  | Yes Refl = Yes Refl
  decBasic (SymbolIsBasic s1)  (SymbolIsBasic s2)  | No cntr = No ?decBasicSymbolNop
decBasic (SymbolIsBasic s1)  (PairIsBasic x1 y2) = No uninhSymbolPair
decBasic (PairIsBasic x1 y1) BoolIsBasic         = No (negEqSymBasic uninhBoolPair)
decBasic (PairIsBasic x1 y1) IntIsBasic          = No (negEqSymBasic uninhIntPair)
decBasic (PairIsBasic x1 y1) StringIsBasic       = No (negEqSymBasic uninhStringPair)
decBasic (PairIsBasic x1 y1) UnitIsBasic         = No (negEqSymBasic uninhUnitPair)
decBasic (PairIsBasic x1 y1) (SymbolIsBasic s2)  = No (negEqSymBasic uninhSymbolPair)
decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y2) with (decBasic x1 x2, decBasic y1 y2)
  decBasic (PairIsBasic x1 y1) (PairIsBasic x1 y1) | (Yes Refl, Yes Refl) = Yes Refl
  decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y1) | (No cntr1, Yes Refl) = No ?decBasicPairNopYes
  decBasic (PairIsBasic x1 y1) (PairIsBasic x1 y2) | (Yes Refl, No cntr2) = No ?decBasicPairYesNop
  decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y2) | (No cntr1, No cntr2) = No ?decBasicPairNopNop

neqBasic : Not (IsBasic a = IsBasic b) -> Not (a = b)
neqBasic f Refl = f Refl

neqDPair : {a1 : Type} -> {a2 : Type} -> {p1 : IsBasic a1} -> {p2 : IsBasic a2} -> Not (p1 = p2) -> Not ((a1 ** p1) = (a2 ** p2))
neqDPair contra Refl = contra Refl

export
DecEq BasicType where
  decEq (a1 ** p1) (a2 ** p2) with (decBasic p1 p2)
    decEq (a1 ** p1) (a1 ** p1) | Yes Refl = Yes Refl
    decEq (a1 ** p1) (a2 ** p2) | No contra = No (neqDPair contra)
