module Data.Symbolic

import Helpers
-- import Data.Basic

%default total

---- Symbols -------------------------------------------------------------------

export
Id : Type
Id = Nat

public export
data Symbolic : Type -> Type where
  Concrete : a -> Symbolic a
  Symbol : (a : Type) -> Id -> Symbolic a
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

-- C : {auto a : Type} -> a -> Symbolic a
-- C = Concrete

-- S : (a : Type) -> {auto ok : IsBasic a} -> Id -> Symbolic a
-- S = Symbol

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
Eq a => Eq (Symbolic a) where
  (==) (Concrete x1)  (Concrete x2)  = x1 == x2
  (==) (Symbol a k1)  (Symbol a k2)  = k1 == k2
  (==) (Not x1)       (Not x2)       = x1 == x2
  (==) (x1 &&. z1)    (x2 &&. z2)    = x1 == x2 && z1 == z2
  (==) (x1 ||. z1)    (x2 ||. z2)    = x1 == x2 && z1 == z2
  (==) (x1 =>. z1)    (x2 =>. z2)    = x1 == x2 && z1 == z2
  (==) (x1 <. z1)     (x2 <. z2)     = x1 == x2 && z1 == z2
  (==) (x1 <=. z1)    (x2 <=. z2)    = x1 == x2 && z1 == z2
  (==) (x1 ==. z1)    (x2 ==. z2)    = x1 == x2 && z1 == z2
  (==) (x1 /=. z1)    (x2 /=. z2)    = x1 == x2 && z1 == z2
  (==) (x1 >=. z1)    (x2 >=. z2)    = x1 == x2 && z1 == z2
  (==) (x1 >. z1)     (x2 >. z2)     = x1 == x2 && z1 == z2
  (==) (x1 +. z1)     (x2 +. z2)     = x1 == x2 && z1 == z2
  (==) (x1 -. z1)     (x2 -. z2)     = x1 == x2 && z1 == z2
  (==) (x1 *. z1)     (x2 *. z2)     = x1 == x2 && z1 == z2
  (==) (x1 /. z1)     (x2 /. z2)     = x1 == x2 && z1 == z2
  (==) (x1 %. z1)     (x2 %. z2)     = x1 == x2 && z1 == z2
  (==) _              _              = False

export
Eq1 Symbolic where
  eq1 (Concrete x1)  (Concrete x2)  = x1 == x2
  eq1 (Symbol a k1)  (Symbol a k2)  = k1 == k2
  eq1 (Not x1)       (Not x2)       = x1 == x2
  eq1 (x1 &&. z1)    (x2 &&. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 ||. z1)    (x2 ||. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 =>. z1)    (x2 =>. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 <. z1)     (x2 <. z2)     = x1 == x2 && z1 == z2
  eq1 (x1 <=. z1)    (x2 <=. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 ==. z1)    (x2 ==. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 /=. z1)    (x2 /=. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 >=. z1)    (x2 >=. z2)    = x1 == x2 && z1 == z2
  eq1 (x1 >. z1)     (x2 >. z2)     = x1 == x2 && z1 == z2
  eq1 (x1 +. z1)     (x2 +. z2)     = x1 == x2 && z1 == z2
  eq1 (x1 -. z1)     (x2 -. z2)     = x1 == x2 && z1 == z2
  eq1 (x1 *. z1)     (x2 *. z2)     = x1 == x2 && z1 == z2
  eq1 (x1 /. z1)     (x2 /. z2)     = x1 == x2 && z1 == z2
  eq1 (x1 %. z1)     (x2 %. z2)     = x1 == x2 && z1 == z2
  eq1 _              _              = False

-- ite : Symbolic Bool -> Symbolic a -> Symbolic a -> Symbolic a
-- ite (Concrete b) x y = if b then x else y
-- ite s x y = Ite s x y

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
end : a -> Simulation a
end x = x !! Concrete True

export
||| Simplifying path:   remove tautologies
||| Simplifying routes: remove route with unsat path
ifThenElse : Simulation (Symbolic Bool) -> Simulation (Symbolic a) -> Simulation (Symbolic a) -> List (Simulation (Symbolic a))
ifThenElse (Concrete True  !! p1) (v2 !! p2) _          = [ v2 !! p1 ++ p2 ]
ifThenElse (Concrete False !! p1) _          (v3 !! p3) = [ v3 !! p1 ++ p3 ]
ifThenElse (b1 !! p1)             (v2 !! p2) (v3 !! p3) = [ v2 !! p1 ++ p2 ++ b1, v3 !! p1 ++ p3 ++ Not b1 ]
