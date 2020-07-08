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
DecInj IsBasic where
  decInj {a=Bool}     {b=Bool}     (BoolIsBasic)       (BoolIsBasic)       = Yes Refl
  decInj {a=Int}      {b=Int}      (IntIsBasic)        (IntIsBasic)        = Yes Refl
  decInj {a=String}   {b=String}   (StringIsBasic)     (StringIsBasic)     = Yes Refl
  decInj {a=()}       {b=()}       (UnitIsBasic)       (UnitIsBasic)       = Yes Refl
  decInj {a=(a1, b1)} {b=(a2, b2)} (PairIsBasic x1 y1) (PairIsBasic x2 y2) = case (decInj x1 x2, decInj y1 y2) of
                                                                                   (Yes Refl, Yes Refl) => Yes Refl
                                                                                   (_, _) => No believe_me
  decInj {a=_}        {b=_}        _                      _                = No believe_me

export
neqBasic : Not (IsBasic a = IsBasic b) -> Not (a = b)
neqBasic f Refl = f Refl

export
(?:) : a -> {auto p : IsBasic a} -> b -> {auto q : IsBasic b} -> Dec (a = b)
(?:) _ {p} _ {q} = decInj p q
