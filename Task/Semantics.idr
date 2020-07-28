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
  | CouldNotPick
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
normalise : Task h a -> (Stream Nat, State h) -> ((t : Task h a ** IsNormal t), (Stream Nat, State h))
---- Step
normalise (Step t1 e2) s =
  let ((t1' ** n1'), s') = normalise t1 s
      stay = (Step t1' e2 ** StepIsNormal n1')
   in case value t1' (get s') of
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
  let ((t1' ** n1'), s') = normalise t1 s
   in case value t1' (get s') of
    Just _ => ((t1' ** n1'), s') -- N-ChooseLeft
    Nothing =>
      let ((t2' ** n2'), s'') = normalise t2 s'
       in case value t2' (get s'') of
        Just _ => ((t2' ** n2'), s'') -- N-ChooseRight
        Nothing => ((Choose t1' t2' ** ChooseIsNormal n1' n2'), s'') -- N-ChooseNone
---- Congruences
normalise (Trans f t2) s =
  let ((t2' ** n2'), s') = normalise t2 s
   in ((Trans f t2' ** TransIsNormal n2'), s')
normalise (Pair t1 t2) s =
  let ((t1' ** n1'), s')  = normalise t1 s
      ((t2' ** n2'), s'') = normalise t2 s'
   in ((Pair t1' t2' ** PairIsNormal n1' n2'), s'')
---- Ready
normalise (Done x) s =
  ((Done x ** DoneIsNormal), s)
normalise (Fail) s =
  ((Fail ** FailIsNormal), s)
---- Editors
normalise (Edit Unnamed e) s =
  let (k, s') = fresh s
   in ((Edit (Named k) e ** EditIsNormal), s')
normalise (Edit (Named k) e) s
  = ((Edit (Named k) e ** EditIsNormal), s)
---- Rewrites
normalise (Assert p) s =
  ((Done p ** DoneIsNormal), s)
normalise (Repeat t1) s =
  let ((t1' ** n1'), s') = normalise t1 s
   in ((Step t1' (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])) ** StepIsNormal n1'), s')
  -- normalise (Step t1 (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x]))) s <-- Should be equivallent
-- normalise (Share b) = do
--   l <- Store.alloc b --XXX: raise?
--   pure $ Done l
normalise (Assign b l) s =
  let s' = modify (write b l) s
   in ((Done () ** DoneIsNormal), s')
  -- tell [pack r]

---- Handling ------------------------------------------------------------------

public export
handle' : Editor h a -> Concrete -> State h -> Either NotApplicable (Editor h a, State h)
handle' (Enter {a} {ok}) (Value {a'} {ok'} v') s with (decBasic ok ok')
  handle' (Enter {a} {ok}) (Value {a'=a } {ok'=ok } v') s | Yes Refl = Right (Update v', s)
  handle' (Enter {a} {ok}) (Value {a'=a'} {ok'=ok'} v') s | No _ = Left $ CouldNotChangeVal a' a
handle' (Update {a} {ok} v) (Value {a'} {ok'} v') s with (decBasic ok ok')
  handle' (Update {a} {ok} v) (Value {a'=a } {ok'=ok } v') s | Yes Refl = Right (Update v', s)
  handle' (Update {a} {ok} v) (Value {a'=a'} {ok'=ok'} v') s | No _ = Left $ CouldNotChangeVal a' a
handle' (Change {a} {ok} v) (Value {a'} {ok'} v') s with (decBasic ok ok')
  handle' (Change {a} {ok} l) (Value {a'=a } {ok'=ok } v') s | Yes Refl = Right (Change l, write v' l s)
  handle' (Change {a} {ok} l) (Value {a'=a'} {ok'=ok'} v') s | No _ = Left $ CouldNotChangeRef a' a
handle' (View _) c _ = Left $ CouldNotHandleValue c
handle' (Watch _) c _ = Left $ CouldNotHandleValue c
handle' (Select _) c _ = Left $ CouldNotHandleValue c

public export
pick : Task h a -> Label -> Either NotApplicable (Task h a)
pick t@(Edit n (Select ts)) l =
  case lookup l ts of
    Just t' => do
      if Option n l `elem` options t
        then Right t'
        else Left $ CouldNotGoTo l
    Nothing => Left $ CouldNotFind l
pick (Trans e1 t2) l =
  case pick t2 l of
    Right t' => Right $ Trans e1 t'
    Left e => Left e
pick (Step t1 e2) l =
  case pick t1 l of
    Right t' => Right $ Step t' e2
    Left e => Left e
pick _ _ = Left $ CouldNotPick

public export
handle : (t : Task h a) -> IsNormal t => Input Concrete -> State h -> Either NotApplicable (Task h a, State h)
---- Selections
handle t@(Edit n (Select ts)) (Option n' l) s =
  case n ?= n' of
    Yes Refl => case pick t l of
      Right t' => Right (t', s) -- H-Select
      Left e => Left e
    No _ => Left $ CouldNotMatch n n'
handle (Edit n (Select ts)) i s =
  Left $ CouldNotHandle i
---- Editors
handle (Edit (Named k) e) (Insert k' c) s =
  case k ?= k' of
    Yes Refl => case handle' e c s of
      Right (e', s') => Right (Edit (Named k) e', s') -- H-Edit
      Left e => Left e
    No _ => Left $ CouldNotMatch (Named k) (Named k')
handle (Edit (Named k) e) i@(Option n' l) s =
  Left $ CouldNotHandle i
handle (Edit Unnamed e) i s =
  Left $ CouldNotHandle i
---- Pass
handle (Trans e1 t2) @{TransIsNormal n2} i s =
  case handle t2 i s of
    Right (t2', s') => Right (Trans e1 t2', s') -- H-Trans
    Left e => Left e
handle (Step t1 e2) @{StepIsNormal n1} (Option Unnamed l) s =
  case value t1 s of
    Just v1 => case pick (e2 v1) l of
      Right t' => Right (t', s) -- H-Preselect
      Left e => Left e
    Nothing => Left $ CouldNotContinue
handle (Step t1 e2) @{StepIsNormal n1} i s =
  case handle t1 i s of
    Right (t1', s') => Right (Step t1' e2, s') -- H-Step
    Left _ => Left $ CouldNotHandle i
handle (Pair t1 t2) @{PairIsNormal n1 n2} i s =
  case handle t1 i s of
    Right (t1', s') => Right (Pair t1' t2, s') -- H-PairFirst
    Left _ => case handle t2 i s of
      Right (t2', s') => Right (Pair t1 t2', s') -- H-PairSecond
      Left e => Left e
handle (Choose t1 t2) @{ChooseIsNormal n1 n2} i s =
  case handle t1 i s of
    Right (t1', s') => Right (Choose t1' t2, s') -- H-ChooseFirst
    Left _ => case handle t2 i s of
      Right (t2', s') => Right (Choose t1 t2', s')
      Left e => Left e -- H-ChoosSecond
---- Rest
handle (Done _) i _ = Left $ CouldNotHandle i
handle (Fail) i _ = Left $ CouldNotHandle i


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
