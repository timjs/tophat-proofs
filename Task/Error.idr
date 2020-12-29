module Task.Error

import Helpers
import Data.Some
import Task.Input

---- Errors --------------------------------------------------------------------

public export
data NotApplicable
  = CouldNotMatch Name Name
  | CouldNotChangeVal (Some IsBasic) (Some IsBasic)
  | CouldNotChangeRef (Some IsBasic) (Some IsBasic)
  | CouldNotGoTo Label
  | CouldNotFind Label
  | CouldNotContinue
  | CouldNotHandle (Input Concrete)
  | CouldNotHandleValue Concrete
  | ToFewInputs
  | ToManyInputs (List (Input Concrete))
