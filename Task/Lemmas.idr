module Task.Lemmas

import Helpers
import Data.Vect
import Task.Syntax

all_failing : (ts : Vect n (Task h a)) -> (p : Elem t ts) -> (all failing ts = True) -> Vect n (failing t = True)
