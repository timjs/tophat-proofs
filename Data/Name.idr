module Data.Name

import Helpers
import Data.Stream

%default total

---- Labels --------------------------------------------------------------------

public export
Label : Type
Label = String

---- Identifiers ---------------------------------------------------------------

public export
Id : Type
Id = Nat

export
ids : Stream Id
ids = iterate S 0

---- Names ---------------------------------------------------------------------

public export
data Name
  = Unnamed
  | Named Id

export
Eq Name where
  Unnamed == Unnamed  = True
  Named k == Named k' = k == k'
  _       == _       = False

export
Uninhabited (Unnamed = Named k) where
  uninhabited Refl impossible

export
namedInjective : (Named x = Named k) -> (x = k)
namedInjective Refl = Refl

export
DecEq Name where
  decEq (Unnamed) (Unnamed)  = Yes Refl
  decEq (Named k) (Named k') with (k ?= k')
    decEq (Named k) (Named k)  | Yes Refl = Yes Refl
    decEq (Named k) (Named k') | No contra = No (contra . namedInjective)
  decEq (Unnamed) (Named k)  = No absurd
  decEq (Named k) (Unnamed)  = No (negEqSym absurd)
