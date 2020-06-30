module Task.Prove

import Control.Monad.State
import Data.Basic
import Data.Maybe
import Data.So
import Task.Syntax
import Task.Observe

-- fail_valin : (t : Task h a) -> So (failing t) -> (value t == Nothing, inputs t == [])

valin_fail : Eq (typeOf b) => IsBasic b => (t : Task h b) -> (s : State h) -> So (evalState (value t) s == Nothing) -> So (evalState (inputs t) s == []) -> So (failing t)


----
