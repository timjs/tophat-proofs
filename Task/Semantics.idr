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

get : (Stream Nat, State h) -> State h
get = snd

modify : (State h -> State h) -> (Stream Nat, State h) -> (Stream Nat, State h)
modify f (ns, s) = (ns, f s)

fresh : (Stream Nat, State h) -> (Nat, (Stream Nat, State h))
fresh (n :: ns, s) = (n, (ns, s))

public export
normalise : Task h a -> (Stream Nat, State h) -> (Task h a, (Stream Nat, State h))
---- Step
normalise (Step t1 e2) s =
  let (t1', s') = normalise t1 s
      stay = Step t1' e2
   in case value t1' (snd s') of
    Nothing => (stay, s') -- N-StepNone
    Just v1 =>
      let t2 = e2 v1
       in if failing t2
        then (stay, s') -- N-StepFail
        else if not $ isNil $ options t2
          then (stay, s') -- N-StepWait
          --> Note that Idris2 can't prove termination when writing `t'` instead of `e2 v1`, see #493
          else normalise (e2 v1) s' -- N-StepCont
---- Choose
normalise (Choose t1 t2) s =
  let (t1', s') = normalise t1 s
   in case value t1' (get s') of
    Just _ => (t1', s') -- N-ChooseLeft
    Nothing =>
      let (t2', s'') = normalise t2 s'
       in case value t2' (get s'') of
        Just _ => (t2', s'') -- N-ChooseRight
        Nothing => (Choose t1' t2', s'') -- N-ChooseNone
---- Congruences
normalise (Trans f t2) s =
  let (t2', s') = normalise t2 s
   in (Trans f t2', s')
normalise (Pair t1 t2) s =
  let (t1', s')  = normalise t1 s
      (t2', s'') = normalise t2 s'
   in (Pair t1' t2', s'')
---- Ready
normalise t@(Done _) s = (t, s)
normalise t@(Fail) s = (t, s)
---- Editors
normalise t@(Edit Unnamed e) s =
  let (n, s') = fresh s
   in (Edit (Named n) e, s')
normalise t@(Edit (Named _) _) s = (t, s)
---- Rewrites
normalise (Assert p) s = (Done p, s)
normalise (Repeat t1) s =
  let (t1', s') = normalise t1 s
   in (Step t1' (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])), s')
  -- normalise (Step t1 (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x]))) s <-- Should be equivallent
-- normalise (Share b) = do
--   l <- Store.alloc b --XXX: raise?
--   pure $ Done l
normalise (Assign b l) s =
  let s' = modify (write b l) s
   in (Done (), s')
  -- tell [pack r]

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
handle (Repeat _) s i = Left $ CouldNotHandle i
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
