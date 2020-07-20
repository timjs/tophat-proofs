module Task.Semantics

import Helpers
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

---- Normalisation -------------------------------------------------------------

{-
public export
normalise : Stream Nat -> Task h a -> State h -> (Task h a, State h)
---- Step
normalise ns (Step t1 e2) s =
  let (t1', s') = normalise t1 s
      stay = Step t1' e2
   in case value t1' s' of
    Nothing => (stay, s') -- N-StepNone
    Just v1 =>
      let t2 = e2 v1
      if failing t2
        then (stay, s') -- N-StepFail
        else if not $ isNil $ options t2
          then (stay, s') -- N-StepWait
          else assert_total (normalise t2 s') -- N-StepCont
---- Choose
normalise ns (Choose t1 t2) s = do
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
normalise ns (Trans f t2) s = pure (Trans f) <*> normalise t2
normalise ns (Pair t1 t2) s = pure Pair <*> normalise t1 <*> normalise t2
---- Ready
normalise ns t@(Done _) s = pure t
normalise ns t@(Fail) s = pure t
---- Editors
normalise ns t@(Edit Unnamed e) s = do
    n <- supply
    pure $ Edit (Named n) e
normalise ns t@(Edit (Named _) _) s = pure t
---- Checks
normalise ns (Assert p) s = do
    pure $ Done p
---- References
-- normalise (Share b) = do
--   l <- Store.alloc b --XXX: raise?
--   pure $ Done l
normalise ns (Assign b l) s = do
  modify (write b l)
  -- tell [pack r]
  pure $ Done ()
-}

---- Handling ------------------------------------------------------------------

public export
handle' : Editor h a -> State h -> Concrete -> Either NotApplicable (Editor h a, State h)
handle' (Enter {a} {ok}) s (Value {a'} {ok'} v') with (decBasic ok ok')
  handle' (Enter {a} {ok}) s (Value {a'=a } {ok'=ok } v') | Yes Refl = Right (Update v', s)
  handle' (Enter {a} {ok}) s (Value {a'=a'} {ok'=ok'} v') | No _ = Left $ CouldNotChangeVal a' a
handle' (Update {a} {ok} v) s (Value {a'} {ok'} v') with (decBasic ok ok')
  handle' (Update {a} {ok} v) s (Value {a'=a } {ok'=ok } v') | Yes Refl = Right (Update v', s)
  handle' (Update {a} {ok} v) s (Value {a'=a'} {ok'=ok'} v') | No _ = Left $ CouldNotChangeVal a' a
handle' (Change {a} {ok} v) s (Value {a'} {ok'} v') with (decBasic ok ok')
  handle' (Change {a} {ok} l) s (Value {a'=a } {ok'=ok } v') | Yes Refl = Right (Change l, write v' l s)
  handle' (Change {a} {ok} l) s (Value {a'=a'} {ok'=ok'} v') | No _ = Left $ CouldNotChangeRef a' a
handle' (View _) _ c = Left $ CouldNotHandleValue c
handle' (Watch _) _ c = Left $ CouldNotHandleValue c
handle' (Select _) _ c = Left $ CouldNotHandleValue c

rethrow : Either e (a, s) -> (Either e a, s)

public export
handle : Task h a -> State h -> Input Concrete -> Either NotApplicable (Task h a, State h)
---- Editors
handle t@(Edit n (Select ts)) s (n', Decide l) =
  case n ?= n' of
    Yes Refl => case lookup l ts of
      Just t' => do
        if (n, l) `elem` options t
          then Right (t', s)
          else Left $ CouldNotGoTo l
      Nothing => Left $ CouldNotFind l
    No _ => Left $ CouldNotMatch n n'
--FIXME: Why is this case needed for proofs? It is covered by the last case below...
handle t@(Edit n (Select ts)) s i@(n', Insert c) =
  Left $ CouldNotHandle i
--FIXME: Does this allow sending Enter actions to unnamed editors??
handle (Edit n e) s (n', Insert c) =
  case n ?= n' of
    Yes Refl => case handle' e s c of
      Right (e', s') => Right (Edit n e', s')
      Left e => Left e
    No _ => Left $ CouldNotMatch n n
handle (Edit n e) s i@(n', Decide l) =
  Left $ CouldNotHandle  i
---- Pass
handle (Trans e1 t2) s i =
  case handle t2 s i of
    Right (t2', s') => Right (Trans e1 t2', s')
    Left e => Left e
handle (Step t1 e2) s i =
  case handle t1 s i of
    Right (t1', s') => Right (Step t1' e2, s') -- H-Step
    Left _ => do
      case value t1 s of
        Just v1 => handle (e2 v1) s i -- H-StepCont
        Nothing => Left $ CouldNotContinue
handle (Pair t1 t2) s i =
  case handle t1 s i of
    Right (t1', s') => Right (Pair t1' t2, s') -- H-PairFirst
    Left _ => case handle t2 s i of
      Right (t2', s') => Right (Pair t1 t2', s') -- H-PairSecond
      Left e => Left e
handle (Choose t1 t2) s i =
  case handle t1 s i of
    Right (t1', s') => Right (Choose t1' t2, s') -- H-ChooseFirst
    Left _ => case handle t2 s i of
      Right (t2', s') => Right (Choose t1 t2', s')
      Left e => Left e -- H-ChoosSecond
---- Rest
handle (Done _) s i = Left $ CouldNotHandle i
handle (Fail) s i = Left $ CouldNotHandle i
handle (Assert _) s i = Left $ CouldNotHandle i
handle (Assign _ _) s i = Left $ CouldNotHandle i


{-
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
    -}
