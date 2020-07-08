module Task.Types

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

export
typEq : IsBasic a -> IsBasic b -> Dec (a = b)
typEq {a=Bool}     {b=Bool}     (BoolIsBasic)       (BoolIsBasic)       = Yes Refl
typEq {a=Int}      {b=Int}      (IntIsBasic)        (IntIsBasic)        = Yes Refl
typEq {a=String}   {b=String}   (StringIsBasic)     (StringIsBasic)     = Yes Refl
typEq {a=()}       {b=()}       (UnitIsBasic)       (UnitIsBasic)       = Yes Refl
typEq {a=(a1, b1)} {b=(a2, b2)} (PairIsBasic x1 y1) (PairIsBasic x2 y2) = case (typEq x1 x2, typEq y1 y2) of
                                                                               (Yes Refl, Yes Refl) => Yes Refl
                                                                               (_, _) => No believe_me
typEq {a=_}        {b=_}        _                      _                = No believe_me
--> We cannot produce above proofs yet because Idris2 has Type : Type...

export
(?:) : a -> (p : IsBasic a) => b -> (q : IsBasic b) => Dec (a = b)
(?:) _ {p} _ {q} = typEq p q
