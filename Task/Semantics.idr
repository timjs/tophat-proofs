module Task.Semantics

import Helpers
import Control.Monad.State
import Control.Monad.Supply
import Data.List
import Task.Syntax
import Task.Observations

---- Errors --------------------------------------------------------------------

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

okay : Monad m => a -> m (Either e a)
okay = pure . Right

throw : Monad m => e -> m (Either e a)
throw = pure . Left

rethrow : Monad m => Either e a -> (a -> b) -> m (Either e b)
rethrow (Left e)  _ = throw e
rethrow (Right x) f = okay $ f x

---- Normalisation -------------------------------------------------------------

normalise :
  MonadSupply Nat m =>
  MonadState (State h) m =>
  Task h a ->
  m (Task h a)
normalise t = case t of
  ---- Step
  Step t1 e2 => do
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
              else normalise t2 -- N-StepCont

  ---- Choose
  Choose t1 t2 => do
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
  Trans f t2 => pure (Trans f) <*> normalise t2
  Pair t1 t2 => pure Pair <*> normalise t1 <*> normalise t2
  ---- Ready
  Done _ => pure t
  Fail => pure t
  ---- Editors
  Edit Unnamed e => do
    n <- supply
    pure $ Edit (Named n) e
  Edit (Named _) _ => pure t
  ---- Checks
  Assert p => do
    pure $ Done p
  ---- References
  -- Share b => do
  --   l <- Store.alloc b --XXX: raise?
  --   pure $ Done l
  Assign b l => do
    modify (write b l)
    -- tell [pack r]
    pure $ Done ()

---- Handling ------------------------------------------------------------------

handle' :
  MonadState (State h) m =>
  Concrete ->
  Editor h a ->
  m (Either NotApplicable (Editor h a))
handle' (AConcrete {a'} {ok'} v') (Enter {a} {ok}) with (decBasic ok' ok)
  handle' (AConcrete {a'=a } {ok'=ok } v') (Enter {a} {ok}) | Yes Refl = okay $ Update v'
  handle' (AConcrete {a'=a'} {ok'=ok'} v') (Enter {a} {ok}) | No _ = throw $ CouldNotChangeVal a' a
handle' (AConcrete {a'} {ok'} v') (Update {a} {ok} v) with (decBasic ok' ok)
  handle' (AConcrete {a'=a } {ok'=ok } v') (Update {a} {ok} v) | Yes Refl = okay $ Update v'
  handle' (AConcrete {a'=a'} {ok'=ok'} v') (Update {a} {ok} v) | No _ = throw $ CouldNotChangeVal a' a
handle' (AConcrete {a'} {ok'} v') (Change {a} {ok} v) with (decBasic ok' ok)
  handle' (AConcrete {a'=a } {ok'=ok } v') (Change {a} {ok} l) | Yes Refl = modify (write v' l) *> okay (Change l)
  handle' (AConcrete {a'=a'} {ok'=ok'} v') (Change {a} {ok} l) | No _ = throw $ CouldNotChangeRef a' a
handle' c _ = throw $ CouldNotHandleValue c

handle :
  MonadState (State h) m =>
  Task h a ->
  Input Concrete ->
  m (Either NotApplicable (Task h a))
{-
handle t i = case t of
  ---- Editors
  Edit n e => case i of
    IOption n' l => case e of
      Select ts => if n == n'
        then case HashMap.lookup l ts of
          Nothing => throw $ CouldNotFind l
          Just t' => do
            let os = options t
            if Option n l `elem` os
              then pure t'
              else throw $ CouldNotGoTo l
        else throw $ CouldNotMatch n n'
      _ => throw $ CouldNotHandle i
    IEnter m b' => if n == Named m
      then do
        e' <- handle' b' e
        pure $ Edit n e'
      else throw $ CouldNotMatch n (Named m)
      -}
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
handle _ i = throw $ CouldNotHandle i


---- Fixation ------------------------------------------------------------------

fixate :
  MonadSupply Nat m =>
  MonadState (State h) m =>
  Task h a ->
  m (Task h a)
fixate t = do
  -- (d, t') <- runWriter t
  -- (d', t'') <- normalise t' |> runWriter
  t'' <- normalise t
  -- log Info $ DidNormalise (display t'')
  -- let ws = watching t''
  -- let ds = d `union` d'
  -- let os = ds `intersect` ws
  -- case os of
    -- [] => do
      -- log Info $ DidStabilise (length ds) (length ws)
      -- let t''' = balance t''
      -- log Info $ DidBalance (display t''')
  pure t'' -- F-Done
    -- _ => do
      -- log Info $ DidNotStabilise (length ds) (length ws) (length os)
      -- fixate $ pure t'' -- F-Loop

---- Initialisation ------------------------------------------------------------

initialise :
  MonadSupply Nat m =>
  MonadState (State h) m =>
  Task h a ->
  m (Task h a)
initialise t = do
  -- log Info $ DidStart (display t)
  fixate t

---- Interaction ---------------------------------------------------------------

interact :
  MonadSupply Nat m =>
  MonadState (State h) m =>
  Task h a ->
  Input Concrete ->
  m (Task h a)
interact t i = do
  xt <- handle t i
  case xt of
    Left e => do
      -- log Warning e
      pure t
    Right t' => fixate t'
