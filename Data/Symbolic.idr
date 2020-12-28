module Data.Symbolic

import Helpers
import Data.Name
import Data.Stream

%default total

---- Symbols -------------------------------------------------------------------

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
  -- Fst : (Show a, Show b) => Symbolic (a, b) -> Symbolic a
  -- Snd : (Show a, Show b) => Symbolic (a, b) -> Symbolic b
  -- (**.) : (Eq a, Eq b) => (Show a, Show b) => Symbolic a -> Symbolic b -> Symbolic (a, b)

---- Paths and Simulations -----------------------------------------------------

export
Path : Type
Path = Symbolic Bool

infixr 3 ++

export
(++) : Path -> Path -> Path
(++) = (&&.)

public export
data Simulation : Type -> Type where
  (!!) : (x : a) -> (p : Path) -> Simulation a

infix 0 !!

export
final : a -> Simulation a
final x = x !! Value True

-- export
||| Simplifying path:   remove tautologies
||| Simplifying routes: remove route with unsat path
ifThenElse : Simulation (Symbolic Bool) -> Simulation (Symbolic a) -> Simulation (Symbolic a) -> List (Simulation (Symbolic a))
ifThenElse (Value True  !! p1) (v2 !! p2) _          = [ v2 !! p1 ++ p2 ]
ifThenElse (Value False !! p1) _          (v3 !! p3) = [ v3 !! p1 ++ p3 ]
ifThenElse (b1 !! p1)             (v2 !! p2) (v3 !! p3) = [ v2 !! p1 ++ p2 ++ b1, v3 !! p1 ++ p3 ++ Not b1 ]

-- ite : Symbolic Bool -> Symbolic a -> Symbolic a -> Symbolic a
-- ite (Value b) x y = if b then x else y
-- ite s x y = Ite s x y

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
-- infixr 0 **.

---- Equality ------------------------------------------------------------------

export
Eq (Token a) where
  (==) (Fresh a k1) (Fresh a k2) = k1 == k2

mutual

  export
  Eq a => Eq (Symbolic a) where
    z1 == z2 = eq1 z1 z2

  export
  Eq1 Symbolic where
    eq1 (Value x1)     (Value x2)     = x1 == x2
    eq1 (Symbol z1)    (Symbol z2)    = z1 == z2
    eq1 (Not x1)       (Not x2)       = eq1 x1 x2
    eq1 (x1 &&. y1)    (x2 &&. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 ||. y1)    (x2 ||. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 =>. y1)    (x2 =>. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 <. y1)     (x2 <. y2)     = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 <=. y1)    (x2 <=. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 ==. y1)    (x2 ==. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 /=. y1)    (x2 /=. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 >=. y1)    (x2 >=. y2)    = eq1 x1 x2 && eq1 y1 y2
    eq1 (Neg x1)       (Neg x2)       = eq1 x1 x2
    eq1 (x1 >. y1)     (x2 >. y2)     = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 +. y1)     (x2 +. y2)     = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 -. y1)     (x2 -. y2)     = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 *. y1)     (x2 *. y2)     = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 /. y1)     (x2 /. y2)     = eq1 x1 x2 && eq1 y1 y2
    eq1 (x1 %. y1)     (x2 %. y2)     = eq1 x1 x2 && eq1 y1 y2
    -- eq1 (Fst x1)       (Fst x2)       = eq1 x1 x2
    -- eq1 (Snd x1)       (Snd x2)       = eq1 x1 x2
    --NOTE: We have to explicitly pass `Eq a` and `Eq b` because Idris doesn't know both are the same.
    -- eq1 (x1 **. y1)    ((**.) @{(eq_a, eq_b)} x2 y2) = eq1 @{eq_a} x1 x2 && eq1 @{eq_b} y1 y2
    --NOTE: With below enumeration trick we make sure not to forget new cases when added.
    eq1 (Value x1)     _              = False
    eq1 (Symbol z1)    _              = False
    eq1 (Not x1)       _              = False
    eq1 (x1 &&. y1)    _              = False
    eq1 (x1 ||. y1)    _              = False
    eq1 (x1 =>. y1)    _              = False
    eq1 (x1 <. y1)     _              = False
    eq1 (x1 <=. y1)    _              = False
    eq1 (x1 ==. y1)    _              = False
    eq1 (x1 /=. y1)    _              = False
    eq1 (x1 >=. y1)    _              = False
    eq1 (Neg x1)       _              = False
    eq1 (x1 >. y1)     _              = False
    eq1 (x1 +. y1)     _              = False
    eq1 (x1 -. y1)     _              = False
    eq1 (x1 *. y1)     _              = False
    eq1 (x1 /. y1)     _              = False
    eq1 (x1 %. y1)     _              = False
    -- eq1 (Fst x1)       _              = False
    -- eq1 (Snd x1)       _              = False
    -- eq1 (x1 **. y1)    _              = False

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
  -- show (x **. y)    = "(" ++ show x ++ ", " ++ show y ++ ")"
  -- show (Fst x)      = "fst " ++ show x
  -- show (Snd x)      = "snd " ++ show x
