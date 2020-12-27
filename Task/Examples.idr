module Task.Examples

import Helpers
import Task.Syntax

import Data.Fuel
import Task.State
import Task.Semantics

absolute : Task None (Symbolic Int)
absolute =
  Edit Unnamed Enter `Step` \x =>
  Guard [ x >. Value 0 ~> Edit Unnamed (View x) ]