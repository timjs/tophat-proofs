module Task.Observe

import Control.Monoidal
import Control.Monad.State
import Data.List
import Task.Syntax

---- Values --------------------------------------------------------------------

value' : MonadState (State Single) m => Editor Single a -> m (Maybe a)
value' (Enter)    = pure Nothing
value' (Update b) = pure (Just b)
value' (View b)   = pure (Just b)
value' (Select _) = pure Nothing
value' (Change l) = pure Just <*> gets (read l)
value' (Watch l)  = pure Just <*> gets (read l)

value : MonadState (State Single) m => Task Single a -> m (Maybe a)
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

---- Failing -------------------------------------------------------------------

mutual
  failing' : Editor h a -> Bool
  failing' (Enter)     = False
  failing' (Update _)  = False
  failing' (View _)    = False
  failing' (Select ts) = all (failing . snd) ts
  failing' (Change _)  = False
  failing' (Watch _)   = False

  failing : Task h a -> Bool
  failing (Edit _ e)     = failing' e
  failing (Trans _ t2)   = failing t2
  failing (Pair t1 t2)   = failing t1 && failing t2
  failing (Done _)       = False
  failing (Choose t1 t2) = failing t1 && failing t2
  failing (Fail)         = True
  failing (Step t1 _)    = failing t1
  failing (Assert _)     = False
  -- failing (Share _)      = False
  failing (Assign _ _)   = False

---- Options -------------------------------------------------------------------

options' : List (Label, Task h a) -> List Label
options' = map fst . filter (not . failing . snd)

options : Task h a -> List Option
options (Edit n (Select ts)) = map (AOption n) $ options' ts
options (Trans _ t2)         = options t2
options (Step t1 _)          = options t1
options (_)                  = []

---- Inputs --------------------------------------------------------------------

infixl 1 #
(#) : a -> (a -> b) -> b
(#) x f = f x

inputs' : {b : Type} -> Editor h b -> List Dummy
inputs' (Enter)    = [ADummy b]
inputs' (Update _) = [ADummy b]
inputs' (View _)   = []
inputs' (Select _) = [] --NOTE: selections do not have `IEnter` actions and are handles separately
inputs' (Change _) = [ADummy b]
inputs' (Watch _)  = []

inputs : MonadState (State Single) m => Task Single a -> m (List (Input Dummy))
inputs (Edit Unnamed _)               = pure []
inputs (Edit (Named n) (Select ts))   = options' ts # map (ISelect n) # pure
inputs (Edit (Named n) e)             = inputs' e # map (IEnter n) # pure
inputs (Trans _ t2)                   = inputs t2
inputs (Pair t1 t2)                   = pure (++) <*> inputs t1 <*> inputs t2
inputs (Done _)                       = pure []
inputs (Choose t1 t2)                 = pure (++) <*> inputs t1 <*> inputs t2
inputs (Fail)                         = pure []
inputs (Step t1 e2)                   = pure (++) <*> inputs t1 <*> do
                                          mv1 <- value t1
                                          case mv1 of
                                            Nothing => pure []
                                            Just v1 => do
                                              let t2 = e2 v1
                                              options t2 # map fromOption # pure
inputs (Assert _)                     = pure []
-- inputs (Share _)                      = pure []
inputs (Assign _ _)                   = pure []
