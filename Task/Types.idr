module Task.Types

import Helpers

%default total

---- IsBasic data -----------------------------------------------------------

public export
data IsBasic : Type -> Type where
  BoolIsBasic   : IsBasic Bool
  IntIsBasic    : IsBasic Int
  StringIsBasic : IsBasic String
  UnitIsBasic   : IsBasic ()
  PairIsBasic   : IsBasic a -> IsBasic b -> IsBasic (a, b)

---- IsBasic equality -------------------------------------------------------

infix 6 ?:

public export
decBasic : (b1 : IsBasic a1) -> (b2 : IsBasic a2) -> Dec (b1 = b2)
decBasic (BoolIsBasic)       (BoolIsBasic)       = Yes Refl
decBasic (IntIsBasic)        (IntIsBasic)        = Yes Refl
decBasic (StringIsBasic)     (StringIsBasic)     = Yes Refl
decBasic (UnitIsBasic)       (UnitIsBasic)       = Yes Refl
decBasic (PairIsBasic x1 y1) (PairIsBasic x2 y2) = case (decBasic x1 x2, decBasic y1 y2) of
                                                   (Yes Refl, Yes Refl) => Yes Refl
                                                   (_, _) => No believe_me
decBasic _                      _                = No believe_me

export
neqBasic : Not (IsBasic a = IsBasic b) -> Not (a = b)
neqBasic f Refl = f Refl

export
(?:) : a -> {auto p : IsBasic a} -> b -> {auto q : IsBasic b} -> Dec (p = q)
(?:) _ {p} _ {q} = decBasic p q
