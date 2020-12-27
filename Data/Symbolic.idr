module Data.Symbolic

import Helpers
-- import Data.Basic

%default total

---- Symbols -------------------------------------------------------------------

public export
Id : Type
Id = Nat

public export
data Token : Type -> Type where
  Fresh : (a : Type) -> Id -> Token a

public export
data Symbolic : Type -> Type where
  Value : a -> Symbolic a
  Symbol : Token a -> Symbolic a
  -- Logical
  -- Ite : Symbolic Bool -> Symbolic a -> Symbolic a -> Symbolic a
  Not : Symbolic Bool -> Symbolic Bool
  (&&.) : Symbolic Bool -> Symbolic Bool -> Symbolic Bool
  (||.) : Symbolic Bool -> Symbolic Bool -> Symbolic Bool
  (=>.) : Symbolic Bool -> Symbolic Bool -> Symbolic Bool
  -- Equational
  (<.) : Symbolic Int -> Symbolic Int -> Symbolic Bool
  (<=.) : Symbolic Int -> Symbolic Int -> Symbolic Bool
  (==.) : Symbolic Int -> Symbolic Int -> Symbolic Bool
  (/=.) : Symbolic Int -> Symbolic Int -> Symbolic Bool
  (>=.) : Symbolic Int -> Symbolic Int -> Symbolic Bool
  (>.) : Symbolic Int -> Symbolic Int -> Symbolic Bool
  -- Numerical
  Neg : Symbolic Int -> Symbolic Int
  (+.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (-.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (*.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (/.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (%.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  -- Tuples
  -- Tuple : Symbolic a -> Symbolic b -> Symbolic (a, b)
  -- Fst : Symbolic (a, b) -> Symbolic a
  -- Snd : Symbolic (a, b) -> Symbolic b

---- Paths and Simulations -----------------------------------------------------

public export
Path : Type
Path = Symbolic Bool

infixr 3 ++

public export
(++) : Path -> Path -> Path
(++) = (&&.)

public export
data Simulation : Type -> Type where
  (!!) : (x : a) -> (p : Path) -> Simulation a

infix 0 !!

export
final : a -> Simulation a
final x = x !! Value True

export
||| Simplifying path:   remove tautologies
||| Simplifying routes: remove route with unsat path
ifThenElse : Simulation (Symbolic Bool) -> Simulation (Symbolic a) -> Simulation (Symbolic a) -> List (Simulation (Symbolic a))
ifThenElse (Value True  !! p1) (v2 !! p2) _          = [ v2 !! p1 ++ p2 ]
ifThenElse (Value False !! p1) _          (v3 !! p3) = [ v3 !! p1 ++ p3 ]
ifThenElse (b1 !! p1)             (v2 !! p2) (v3 !! p3) = [ v2 !! p1 ++ p2 ++ b1, v3 !! p1 ++ p3 ++ Not b1 ]

---- Fixities ------------------------------------------------------------------

infixl 7 *.
infixl 7 /.
infixl 7 %.

infixl 6 +.
infixl 6 -.

infix  4 <.
infix  4 <=.
infix  4 ==.
infix  4 /=.
infix  4 >=.
infix  4 >.

infixr 3 &&.

infixr 2 ||.

infixr 1 =>.

---- Equality ------------------------------------------------------------------

export
Eq (Token a) where
  (==) (Fresh a k1) (Fresh a k2) = k1 == k2

export
Eq a => Eq (Symbolic a) where
  (==) (Value x1)     (Value x2)     = x1 == x2
  (==) (Symbol z1)    (Symbol z2)    = z1 == z2
  (==) (Not x1)       (Not x2)       = x1 == x2
  (==) (x1 &&. y1)    (x2 &&. y2)    = x1 == x2 && y1 == y2
  (==) (x1 ||. y1)    (x2 ||. y2)    = x1 == x2 && y1 == y2
  (==) (x1 =>. y1)    (x2 =>. y2)    = x1 == x2 && y1 == y2
  (==) (x1 <. y1)     (x2 <. y2)     = x1 == x2 && y1 == y2
  (==) (x1 <=. y1)    (x2 <=. y2)    = x1 == x2 && y1 == y2
  (==) (x1 ==. y1)    (x2 ==. y2)    = x1 == x2 && y1 == y2
  (==) (x1 /=. y1)    (x2 /=. y2)    = x1 == x2 && y1 == y2
  (==) (x1 >=. y1)    (x2 >=. y2)    = x1 == x2 && y1 == y2
  (==) (Neg x1)       (Neg x2)       = x1 == x2
  (==) (x1 >. y1)     (x2 >. y2)     = x1 == x2 && y1 == y2
  (==) (x1 +. y1)     (x2 +. y2)     = x1 == x2 && y1 == y2
  (==) (x1 -. y1)     (x2 -. y2)     = x1 == x2 && y1 == y2
  (==) (x1 *. y1)     (x2 *. y2)     = x1 == x2 && y1 == y2
  (==) (x1 /. y1)     (x2 /. y2)     = x1 == x2 && y1 == y2
  (==) (x1 %. y1)     (x2 %. y2)     = x1 == x2 && y1 == y2
  (==) _              _              = False

export
Eq1 Symbolic where
  eq1 (Value x1)     (Value x2)     = x1 == x2
  eq1 (Symbol z1)    (Symbol z2)    = z1 == z2
  eq1 (Not x1)       (Not x2)       = x1 == x2
  eq1 (x1 &&. y1)    (x2 &&. y2)    = x1 == x2 && y1 == y2
  eq1 (x1 ||. y1)    (x2 ||. y2)    = x1 == x2 && y1 == y2
  eq1 (x1 =>. y1)    (x2 =>. y2)    = x1 == x2 && y1 == y2
  eq1 (x1 <. y1)     (x2 <. y2)     = x1 == x2 && y1 == y2
  eq1 (x1 <=. y1)    (x2 <=. y2)    = x1 == x2 && y1 == y2
  eq1 (x1 ==. y1)    (x2 ==. y2)    = x1 == x2 && y1 == y2
  eq1 (x1 /=. y1)    (x2 /=. y2)    = x1 == x2 && y1 == y2
  eq1 (x1 >=. y1)    (x2 >=. y2)    = x1 == x2 && y1 == y2
  eq1 (Neg x1)       (Neg x2)       = x1 == x2
  eq1 (x1 >. y1)     (x2 >. y2)     = x1 == x2 && y1 == y2
  eq1 (x1 +. y1)     (x2 +. y2)     = x1 == x2 && y1 == y2
  eq1 (x1 -. y1)     (x2 -. y2)     = x1 == x2 && y1 == y2
  eq1 (x1 *. y1)     (x2 *. y2)     = x1 == x2 && y1 == y2
  eq1 (x1 /. y1)     (x2 /. y2)     = x1 == x2 && y1 == y2
  eq1 (x1 %. y1)     (x2 %. y2)     = x1 == x2 && y1 == y2
  eq1 _              _              = False

-- ite : Symbolic Bool -> Symbolic a -> Symbolic a -> Symbolic a
-- ite (Value b) x y = if b then x else y
-- ite s x y = Ite s x y

---- Show ----------------------------------------------------------------------

export
Show (Token a) where
  show (Fresh _ k) = "z" ++ show k

export
Show a => Show (Symbolic a) where
  show (Value x)    = show x
  show (Symbol z)   = show z
  show (Not x)      = "not " ++ show x
  show (x &&. y)    = show x ++ " && " ++ show y
  show (x ||. y)    = show x ++ " || " ++ show y
  show (x =>. y)    = show x ++ " => " ++ show y
  show (x <. y)     = show x ++ " < "  ++ show y
  show (x <=. y)    = show x ++ " <= " ++ show y
  show (x ==. y)    = show x ++ " == " ++ show y
  show (x /=. y)    = show x ++ " /= " ++ show y
  show (x >=. y)    = show x ++ " >= " ++ show y
  show (x >. y)     = show x ++ " > "  ++ show y
  show (Neg x)      = "neg " ++ show x
  show (x +. y)     = show x ++ " + "  ++ show y
  show (x -. y)     = show x ++ " - "  ++ show y
  show (x *. y)     = show x ++ " * "  ++ show y
  show (x /. y)     = show x ++ " / "  ++ show y
  show (x %. y)     = show x ++ " % "  ++ show y
