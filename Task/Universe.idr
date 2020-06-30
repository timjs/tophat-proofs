module Task.Universe

import public Decidable.Equality
import public Task.Heap

%default total

---- Primitive types -----------------------------------------------------------

public export
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

public export
primOf : PrimTy -> Type
primOf BOOL   = Bool
primOf INT    = Int
primOf STRING = String

---- Full types ----------------------------------------------------------------

public export
data Ty
  = UNIT
  | PAIR Ty Ty
  | REF Heap Ty
  | PRIM PrimTy

---- Lemmas

Uninhabited (UNIT = PAIR _ _) where
  uninhabited Refl impossible

Uninhabited (UNIT = REF _ _) where
  uninhabited Refl impossible

Uninhabited (UNIT = PRIM _) where
  uninhabited Refl impossible

Uninhabited (PAIR _ _ = REF _ _) where
  uninhabited Refl impossible

Uninhabited (PAIR _ _ = PRIM _) where
  uninhabited Refl impossible

Uninhabited (REF _ _ = PRIM _) where
  uninhabited Refl impossible

private
fst_neq : Not (a = a') -> Not (PAIR a b = PAIR a' b)
fst_neq contra Refl = contra Refl

private
snd_neq : Not (b = b') -> Not (PAIR a b = PAIR a b')
snd_neq contra Refl = contra Refl

private
both_neq : Not (a = a') -> Not (b = b') -> Not (PAIR a b = PAIR a' b')
both_neq contra _ Refl = contra Refl

private
ref_neq : Not (a = a') -> Not (REF h a = REF h a')
ref_neq contra Refl = contra Refl

private
heap_neq : Not (h = h') -> Not (REF h a = REF h' a)
heap_neq contra Refl = contra Refl

private
all_neq : Not (h = h') -> Not (a = a') -> Not (REF h a = REF h' a')
all_neq contra _ Refl = contra Refl

private
prim_neq : Not (p = q) -> Not (PRIM p = PRIM q)
prim_neq contra Refl = contra Refl

---- Decidablility

export
DecEq Ty where
  decEq UNIT UNIT                                                 = Yes Refl

  decEq (PAIR a b) (PAIR a' b')   with (decEq a a', decEq b b')
    decEq (PAIR a b) (PAIR a b)   | (Yes Refl,  Yes Refl)         = Yes Refl
    decEq (PAIR a b) (PAIR a b')  | (Yes Refl,  No contra)        = No (snd_neq contra)
    decEq (PAIR a b) (PAIR a' b)  | (No contra, Yes Refl)         = No (fst_neq contra)
    decEq (PAIR a b) (PAIR a' b') | (No contra, No contra')       = No (both_neq contra contra')

  decEq (REF h a)  (REF h' a')   with (decEq h h', decEq a a')
    decEq (REF h a)  (REF h a)   | (Yes Refl,  Yes Refl)          = Yes Refl
    decEq (REF h a)  (REF h a')  | (Yes Refl,  No contra)         = No (ref_neq contra)
    decEq (REF h a)  (REF h' a)  | (No contra, Yes Refl)          = No (heap_neq contra)
    decEq (REF h a)  (REF h' a') | (No contra, No contra')        = No (all_neq contra contra')

  decEq (PRIM p)  (PRIM q)   with (decEq p q)
    decEq (PRIM q)  (PRIM q) | (Yes Refl)                         = Yes Refl
    decEq (PRIM p)  (PRIM q) | (No contra)                        = No (prim_neq contra)

  decEq (UNIT)     (PAIR _ _)                                     = No absurd
  decEq (PAIR _ _) (UNIT)                                         = No (negEqSym absurd)
  decEq (UNIT)     (REF _ _)                                      = No absurd
  decEq (REF _ _)  (UNIT)                                         = No (negEqSym absurd)
  decEq (UNIT)     (PRIM _)                                       = No absurd
  decEq (PRIM _)   (UNIT)                                         = No (negEqSym absurd)

  decEq (PAIR _ _) (REF _ _)                                      = No absurd
  decEq (REF _ _)  (PAIR _ _)                                     = No (negEqSym absurd)
  decEq (PAIR _ _) (PRIM _)                                       = No absurd
  decEq (PRIM _)   (PAIR _ _)                                     = No (negEqSym absurd)

  decEq (REF _ _)  (PRIM _)                                       = No absurd
  decEq (PRIM _)   (REF _ _)                                      = No (negEqSym absurd)

public export
typeOf : Ty -> Type
typeOf UNIT       = ()
typeOf (PAIR a b) = (typeOf a, typeOf b)
typeOf (REF h a)  = Ref h (typeOf a)
typeOf (PRIM p)   = primOf p

---- Basic types ---------------------------------------------------------------

public export
data IsBasic : Ty -> Type where
  UnitIsBasic   : IsBasic UNIT
  BoolIsBasic   : IsBasic (PRIM BOOL)
  IntIsBasic    : IsBasic (PRIM INT)
  StringIsBasic : IsBasic (PRIM STRING)
  PairIsBasic   : IsBasic a -> IsBasic b -> IsBasic (PAIR a b)
