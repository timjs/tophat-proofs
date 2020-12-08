module Data.Symbolic

import Data.Basic

%default total


---- Symbols -------------------------------------------------------------------

Id : Type
Id = Nat

data Symbolic : Type -> Type where
  Concrete : {a : Type} -> a -> Symbolic a
  Symbol : (a : Type) -> {auto ok : IsBasic a} -> Id -> Symbolic a
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
  (+.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (-.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (*.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (/.) : Symbolic Int -> Symbolic Int -> Symbolic Int
  (%.) : Symbolic Int -> Symbolic Int -> Symbolic Int

C : {a : Type} -> a -> Symbolic a
C = Concrete

-- S : (a : Type) -> {auto ok : IsBasic a} -> Id -> Symbolic a
-- S = Symbol

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

-- ite : Symbolic Bool -> Symbolic a -> Symbolic a -> Symbolic a
-- ite (Concrete b) x y = if b then x else y
-- ite s x y = Ite s x y

---- Paths and Routes ----------------------------------------------------------

Path : Type
Path = Symbolic Bool

infixr 3 ++

(++) : Path -> Path -> Path
(++) = (&&.)

data Route : Type -> Type where
  (!!) : (x : Symbolic a) -> (p : Path) -> Route a

infix 0 !!

end : {a : Type} -> a -> Route a
end x = Concrete x !! Concrete True

||| Simplifying path:   remove tautologies
||| Simplifying routes: remove route with unsat path
ifThenElse : Route Bool -> Route a -> Route a -> List (Route a)
ifThenElse (Concrete True  !! p1) (v2 !! p2) _          = [ v2 !! p1 ++ p2 ]
ifThenElse (Concrete False !! p1) _          (v3 !! p3) = [ v3 !! p1 ++ p3 ]
ifThenElse (b1 !! p1)             (v2 !! p2) (v3 !! p3) = [ v2 !! p1 ++ p2 ++ b1, v3 !! p1 ++ p3 ++ Not b1 ]
