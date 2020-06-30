module Task.Observe

import Control.Monoidal
import Control.Monad.State
import Task

---- Values --------------------------------------------------------------------

value' :
  MonadState (State Single) m =>
  Editor Single a ->
  m (Maybe a)
value' (Enter)    = pure Nothing
value' (Update b) = pure (Just b)
value' (View b)   = pure (Just b)
value' (Select _) = pure Nothing
value' (Change l) = pure Just <*> gets (read l)
value' (Watch l)  = pure Just <*> gets (read l)

value :
  MonadState (State Single) m =>
  Task Single a ->
  m (Maybe a)
value (Edit Unnamed _)   = pure Nothing
value (Edit (Named _) e) = value' e
value (Trans f t)        = pure (map f) <*> value t
value (Pair t1 t2)       = pure (<&>) <*> value t1 <*> value t2
value (Done v)           = pure (Just v)
value (Choose t1 t2)     = pure (<|>) <*> value t1 <*> value t2
value (Fail)             = pure Nothing
value (Step _ _)         = pure Nothing
value (Assert b)         = pure (Just b)
-- value (Share b)          = pure (Just Loc)
value (Assign _ _)       = pure (Just ())
