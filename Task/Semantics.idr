module Task.Semantics

import Helpers
import Control.Monad.State
import Control.Monad.Supply
import Data.List
import Task.Syntax
import Task.Observations

%default total

---- Errors --------------------------------------------------------------------

export
data NotApplicable
  = CouldNotMatch Name Name
  | CouldNotChangeVal Type Type
  | CouldNotChangeRef Type Type
  | CouldNotGoTo Label
  | CouldNotFind Label
  | CouldNotSelect
  | CouldNotContinue
  | CouldNotHandle (Input Concrete)
  | CouldNotHandleValue Concrete

public export
okay : Monad m => a -> m (Either e a)
okay = pure . Right

public export
throw : Monad m => e -> m (Either e a)
throw = pure . Left

public export
rethrow : Monad m => Either e a -> (a -> b) -> m (Either e b)
rethrow (Left e)  _ = throw e
rethrow (Right x) f = okay $ f x

---- Normalisation -------------------------------------------------------------

public export
normalise : MonadSupply Nat m => MonadState (State h) m =>
  Task h a -> m (Task h a)
---- Step
normalise (Step t1 e2) = do
  t1' <- normalise t1
  let stay = Step t1' e2
  mv1 <- gets $ value t1'
  case mv1 of
    Nothing => pure stay -- N-StepNone
    Just v1 => do
      let t2 = e2 v1
      if failing t2
        then pure stay -- N-StepFail
        else do
          let os = options t2
          if not $ isNil $ os
            then pure stay -- N-StepWait
            else assert_total (normalise t2) -- N-StepCont
---- Choose
normalise (Choose t1 t2) = do
  t1' <- normalise t1
  mv1 <- gets $ value t1'
  case mv1 of
    Just _ => pure t1' -- N-ChooseLeft
    Nothing => do
      t2' <- normalise t2
      mv2 <- gets $ value t2'
      case mv2 of
        Just _ => pure t2' -- N-ChooseRight
        Nothing => pure $ Choose t1' t2' -- N-ChooseNone
---- Congruences
normalise (Trans f t2) = pure (Trans f) <*> normalise t2
normalise (Pair t1 t2) = pure Pair <*> normalise t1 <*> normalise t2
---- Ready
normalise t@(Done _) = pure t
normalise t@(Fail) = pure t
---- Editors
normalise t@(Edit Unnamed e) = do
    n <- supply
    pure $ Edit (Named n) e
normalise t@(Edit (Named _) _) = pure t
---- Checks
normalise (Assert p) = do
    pure $ Done p
---- References
-- normalise (Share b) = do
--   l <- Store.alloc b --XXX: raise?
--   pure $ Done l
normalise (Assign b l) = do
  modify (write b l)
  -- tell [pack r]
  pure $ Done ()

---- Handling ------------------------------------------------------------------

public export
handle' : MonadState (State h) m =>
  Editor h a -> Concrete -> m (Either NotApplicable (Editor h a))
handle' (Enter {a} {ok}) (AConcrete {a'} {ok'} v') with (decBasic ok ok')
  handle' (Enter {a} {ok}) (AConcrete {a'=a } {ok'=ok } v') | Yes Refl = okay $ Update v'
  handle' (Enter {a} {ok}) (AConcrete {a'=a'} {ok'=ok'} v') | No _ = throw $ CouldNotChangeVal a' a
handle' (Update {a} {ok} v) (AConcrete {a'} {ok'} v') with (decBasic ok ok')
  handle' (Update {a} {ok} v) (AConcrete {a'=a } {ok'=ok } v') | Yes Refl = okay $ Update v'
  handle' (Update {a} {ok} v) (AConcrete {a'=a'} {ok'=ok'} v') | No _ = throw $ CouldNotChangeVal a' a
handle' (Change {a} {ok} v) (AConcrete {a'} {ok'} v') with (decBasic ok ok')
  handle' (Change {a} {ok} l) (AConcrete {a'=a } {ok'=ok } v') | Yes Refl = modify (write v' l) *> okay (Change l)
  handle' (Change {a} {ok} l) (AConcrete {a'=a'} {ok'=ok'} v') | No _ = throw $ CouldNotChangeRef a' a
handle' (View _) c = throw $ CouldNotHandleValue c
handle' (Watch _) c = throw $ CouldNotHandleValue c
handle' (Select _) c = throw $ CouldNotHandleValue c

public export
handle : MonadState (State h) m =>
  Task h a -> Input Concrete -> m (Either NotApplicable (Task h a))
---- Editors
handle t@(Edit n (Select ts)) (n', ASelect l) = case n ?= n' of
  Yes Refl => case lookup l ts of
    Nothing => throw $ CouldNotFind l
    Just t' => do
      if (n, l) `elem` options t
        then okay $ t'
        else throw $ CouldNotGoTo l
  No _ => throw $ CouldNotMatch n n'
--FIXME: Why is this case needed for proofs? It is covered by the last case below...
handle t@(Edit n (Select ts)) i@(n', AEnter c) = throw $ CouldNotHandle i
--FIXME: Does this allow sending Enter actions to unnamed editors??
handle (Edit n e) (n', AEnter c) = case n ?= n' of
  Yes Refl => do
    e' <- handle' e c
    rethrow e' $ Edit n
  No _ => throw $ CouldNotMatch n n'
handle (Edit n e) i@(n', ASelect l) = throw $ CouldNotHandle i
---- Pass
handle (Trans e1 t2) i = do
  t2' <- handle t2 i
  rethrow t2' $ Trans e1
handle (Step t1 e2) i = do
  et1' <- handle t1 i
  case et1' of
    Right t1' => okay $ Step t1' e2 -- H-Step
    Left _ => do
      mv1 <- gets $ value t1
      case mv1 of
        Nothing => throw $ CouldNotContinue
        Just v1 => do
          let t2 = e2 v1
          handle t2 i -- H-StepCont
handle (Pair t1 t2) i = do
  et1' <- handle t1 i
  case et1' of
    Right t1' => okay $ Pair t1' t2 -- H-PairFirst
    Left _ => do
      t2' <- handle t2 i
      rethrow t2' $ Pair t1 -- H-PairSecond
handle (Choose t1 t2) i = do
  et1' <- handle t1 i
  case et1' of
    Right t1' => okay $ Choose t1' t2 -- H-ChooseFirst
    Left _ => do
      t2' <- handle t2 i
      rethrow t2' $ Choose t1 -- H-ChoosSecond
---- Rest
handle (Done _) i = throw $ CouldNotHandle i
handle (Fail) i = throw $ CouldNotHandle i
handle (Assert _) i = throw $ CouldNotHandle i
handle (Assign _ _) i = throw $ CouldNotHandle i


---- Fixation ------------------------------------------------------------------

fixate : MonadSupply Nat m => MonadState (State h) m =>
  Task h a -> m (Task h a)
fixate = normalise
  -- (d, t') <- runWriter t
  -- (d', t'') <- normalise t' |> runWriter
  -- t'' <- normalise t
  -- log Info $ DidNormalise (display t'')
  -- let ws = watching t''
  -- let ds = d `union` d'
  -- let os = ds `intersect` ws
  -- case os of
    -- [] => do
      -- log Info $ DidStabilise (length ds) (length ws)
      -- let t''' = balance t''
      -- log Info $ DidBalance (display t''')
  -- pure t'' -- F-Done
    -- _ => do
      -- log Info $ DidNotStabilise (length ds) (length ws) (length os)
      -- fixate $ pure t'' -- F-Loop

---- Initialisation ------------------------------------------------------------

initialise : MonadSupply Nat m => MonadState (State h) m =>
  Task h a -> m (Task h a)
initialise = fixate
  -- log Info $ DidStart (display t)
  -- fixate t

---- Interaction ---------------------------------------------------------------

interact : MonadSupply Nat m => MonadState (State h) m =>
  Task h a -> Input Concrete -> m (Task h a)
interact t i = do
  xt <- handle t i
  case xt of
    Left e => do
      -- log Warning e
      pure t
    Right t' => fixate t'
