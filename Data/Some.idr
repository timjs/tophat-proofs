module Data.Some

import Helpers
import Type.Basic
import Data.Symbolic

%default total

---- Existentials --------------------------------------------------------------

public export
data Some : (Type -> Type) -> Type where
  Pack : IsBasic a => Eq a => f a -> Some f

export
Eq1 f => Eq (Some f) where
  (==) (Pack @{b1} x1) (Pack @{b2} @{eq} x2) with (decBasic b1 b2)
    (==) (Pack @{b}  x1) (Pack @{b}  @{eq} x2) | Yes Refl = eq1 @{eq} x1 x2
    (==) (Pack @{b1} x1) (Pack @{b2} @{eq} x2) | No  cntr = False
