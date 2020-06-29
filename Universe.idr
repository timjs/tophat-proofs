module Universe

import Data.Strings
import Decidable.Equality

%default total

---- Universes -----------------------------------------------------------------

public export
interface DecEq t => Universe t where
  typeOf : t -> Type

---- Primitive types -----------------------------------------------------------

data PrimTy
  = BOOL
  | INT
  | STRING

---- Lemmas

Uninhabited (BOOL = INT) where
  uninhabited Refl impossible

Uninhabited (BOOL = STRING) where
  uninhabited Refl impossible

Uninhabited (INT = STRING) where
  uninhabited Refl impossible

---- Universe

DecEq PrimTy where
  decEq BOOL   BOOL   = Yes Refl
  decEq INT    INT    = Yes Refl
  decEq STRING STRING = Yes Refl
  decEq BOOL   INT    = No absurd
  decEq INT    BOOL   = No (negEqSym absurd)
  decEq BOOL   STRING = No absurd
  decEq STRING BOOL   = No (negEqSym absurd)
  decEq INT    STRING = No absurd
  decEq STRING INT    = No (negEqSym absurd)

Universe PrimTy where
  typeOf BOOL   = Bool
  typeOf INT    = Int
  typeOf STRING = String

---- Normal types --------------------------------------------------------------

data Ty
  = UNIT
  | PAIR Ty Ty
  -- | REF Ty
  | PRIM PrimTy

---- Lemmas

Uninhabited (UNIT = PAIR _ _) where
  uninhabited Refl impossible

-- Uninhabited (UNIT = REF _) where
--   uninhabited Refl impossible

Uninhabited (UNIT = PRIM _) where
  uninhabited Refl impossible

-- Uninhabited (PAIR _ _ = REF _) where
--   uninhabited Refl impossible

Uninhabited (PAIR _ _ = PRIM _) where
  uninhabited Refl impossible

-- Uninhabited (REF _ = PRIM _) where
--   uninhabited Refl impossible

-- private
-- ref_neq : (a = b -> Void) -> (REF a = REF b) -> Void
-- ref_neq contra Refl = contra Refl

private
prim_neq : (p = q -> Void) -> (PRIM p = PRIM q) -> Void
prim_neq contra Refl = contra Refl

private
snd_neq : (b = b' -> Void) -> (PAIR a b = PAIR a b') -> Void
snd_neq contra Refl = contra Refl

private
fst_neq : (a = a' -> Void) -> (PAIR a b = PAIR a' b) -> Void
fst_neq contra Refl = contra Refl

private
both_neq : (a = a' -> Void) -> (b = b' -> Void) -> (PAIR a b = PAIR a' b') -> Void
both_neq contra_a contra_b Refl = contra_a Refl

---- Decidablility

DecEq Ty where
  decEq UNIT UNIT                                                 = Yes Refl

  decEq (PAIR a b) (PAIR a' b')     with (decEq a a')
    decEq (PAIR a b) (PAIR a b')    | (Yes Refl)  with (decEq b b')
      decEq (PAIR a b) (PAIR a b)   | (Yes Refl)  | (Yes Refl)    = Yes Refl
      decEq (PAIR a b) (PAIR a b')  | (Yes Refl)  | (No contra)   = No (snd_neq contra)
    decEq (PAIR a b) (PAIR a' b')   | (No contra) with (decEq b b')
      decEq (PAIR a b) (PAIR a' b)  | (No contra) | (Yes Refl)    = No (fst_neq contra)
      decEq (PAIR a b) (PAIR a' b') | (No contra) | (No contra')  = No (both_neq contra contra')

  -- decEq (REF a)  (REF b)   with (decEq a b)
  --   decEq (REF b)  (REF b) | (Yes Refl)                           = Yes Refl
  --   decEq (REF a)  (REF b) | (No contra)                          = No (ref_neq contra)

  decEq (PRIM p)  (PRIM q)   with (decEq p q)
    decEq (PRIM q)  (PRIM q) | (Yes Refl)                         = Yes Refl
    decEq (PRIM p)  (PRIM q) | (No contra)                        = No (prim_neq contra)

  decEq (UNIT)     (PAIR _ _)                                     = No absurd
  decEq (PAIR _ _) (UNIT)                                         = No (negEqSym absurd)
  -- decEq (UNIT)     (REF _)                                        = No absurd
  -- decEq (REF _)    (UNIT)                                         = No (negEqSym absurd)
  decEq (UNIT)     (PRIM _)                                       = No absurd
  decEq (PRIM _)   (UNIT)                                         = No (negEqSym absurd)

  -- decEq (PAIR _ _) (REF _)                                        = No absurd
  -- decEq (REF _)    (PAIR _ _)                                     = No (negEqSym absurd)
  decEq (PAIR _ _) (PRIM _)                                       = No absurd
  decEq (PRIM _)   (PAIR _ _)                                     = No (negEqSym absurd)

  -- decEq (REF _)    (PRIM _)                                       = No absurd
  -- decEq (PRIM _)   (REF _)                                        = No (negEqSym absurd)

Universe Ty where
  typeOf UNIT       = ()
  typeOf (PAIR a b) = ( typeOf a, typeOf b )
  -- typeOf (REF a)    = Loc (typeOf a)
  typeOf (PRIM p)   = typeOf p
