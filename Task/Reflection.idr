module Task.Reflection

%default total

---- Reflection data -----------------------------------------------------------

public export
data Reflection : Type -> Type where
  BoolReflection   : Reflection Bool
  IntReflection    : Reflection Int
  StringReflection : Reflection String
  UnitReflection   : Reflection ()
  PairReflection   : Reflection a -> Reflection b -> Reflection (a, b)

---- Reflect interface ---------------------------------------------------------

public export
interface Reflect a where
  reflect : Reflection a

public export
Reflect Bool where
  reflect = BoolReflection

public export
Reflect Int where
  reflect = IntReflection

public export
Reflect String where
  reflect = StringReflection

public export
Reflect () where
  reflect = UnitReflection

public export
Reflect a => Reflect b => Reflect (a, b) where
  reflect = PairReflection reflect reflect

---- Reflection equality -------------------------------------------------------

infix 6 ?:

export
typEq : Reflection a -> Reflection b -> Dec (a = b)
typEq {a=Bool}     {b=Bool}     (BoolReflection)       (BoolReflection)       = Yes Refl
typEq {a=Int}      {b=Int}      (IntReflection)        (IntReflection)        = Yes Refl
typEq {a=String}   {b=String}   (StringReflection)     (StringReflection)     = Yes Refl
typEq {a=()}       {b=()}       (UnitReflection)       (UnitReflection)       = Yes Refl
typEq {a=(a1, b1)} {b=(a2, b2)} (PairReflection x1 y1) (PairReflection x2 y2) = case (typEq x1 x2, typEq y1 y2) of
                                                                                  (Yes Refl, Yes Refl) => Yes Refl
                                                                                  (_, _) => No believe_me
typEq {a=_}        {b=_}        _                      _                      = No believe_me
--> We cannot produce above proofs yet because Idris2 has Type : Type...

export
(?:) : Reflect a => Reflect b => a -> b -> Dec (a = b)
(?:) _ _ = the (Reflection a) reflect `typEq` the (Reflection b) reflect
