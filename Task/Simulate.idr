module Task.Simulate

import Helpers
import Data.Fuel
import Data.List
import Data.Symbolic
import Task.Input
import Task.Syntax
import Task.Observe

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
  | ToFewInputs
  | ToManyInputs (List (Input Concrete))

---- Normalisation -------------------------------------------------------------

public export
normalise : Simulation (Task h a) -> State h -> List (Simulation (Refined (Task h a) IsNormal), State h, Delta h)
---- Step
normalise t@(Step t1 e2 !! p) s = do
  ((t1' ** n1') !! p', s', d') <- normalise (assert_smaller t (t1 !! p)) s
  let stay = (Step t1' e2 ** StepIsNormal n1') !! p'
  case value t1' (get s') of
    Nothing => done (stay, s', d') -- N-StepNone
    Just v1 => do
      let t2 = e2 v1
      if failing t2
        then done (stay, s', d') -- N-StepFail
        else if not $ isNil $ options t2
          then done (stay, s', d') -- N-StepWait
          --NOTE: Idris2 can't prove termination when writing `t2` instead of `e2 v1`, see #493
          else do
            (n2', s'', d'') <- assert_total (normalise (t2 !! p') s')
            done (n2', s'', d' ++ d'') -- N-StepCont
---- Choose
normalise t@(Choose t1 t2 !! p) s = do
  ((t1' ** n1') !! p', s', d') <- normalise (assert_smaller t (t1 !! p)) s
  case value t1' (get s') of
    Just _  => done ((t1' ** n1') !! p', s', d') -- N-ChooseLeft
    Nothing => do
      ((t2' ** n2') !! p'', s'', d'') <- normalise (assert_smaller t (t2 !! p')) s'
      case value t2' (get s'') of
        Just _  => done ((t2' ** n2') !! p'', s'', d' ++ d'') -- N-ChooseRight
        Nothing => done ((Choose t1' t2' ** ChooseIsNormal n1' n2') !! p'', s'', d' ++ d'') -- N-ChooseNone
---- Test
normalise t@(Test b t1 t2 !! p) s =
  let fst = do
        (n1' !! p1', s', d') <- normalise (assert_smaller t (t1 !! p)) s
        done (n1' !! p1' ++ walk b, s', d')
      snd = do
        (n2' !! p2', s', d') <- normalise (assert_smaller t (t2 !! p)) s
        done (n2' !! p2' ++ walk (Not b), s', d')
   in fst <|> snd
---- Converge
normalise t@(Trans f t2 !! p) s = do
  ((t2' ** n2') !! p', s', d') <- normalise (assert_smaller t (t2 !! p)) s
  done ((Trans f t2' ** TransIsNormal n2') !! p', s', d') -- N-Trans
normalise (t@(Pair t1 t2) !! p) s = do
  ((t1' ** n1') !! p' , s' , d' ) <- normalise (assert_smaller t (t1 !! p )) s
  ((t2' ** n2') !! p'', s'', d'') <- normalise (assert_smaller t (t2 !! p')) s'
  done ((Pair t1' t2' ** PairIsNormal n1' n2') !! p'', s'', d' ++ d'') -- N-Pair
---- Ready
normalise (Done x !! p) s =
  done ((Done x ** DoneIsNormal) !! p, s, []) -- N-Done
normalise (Fail !! p) s =
  done ((Fail ** FailIsNormal) !! p, s, []) -- N-Fail
---- Name
normalise (Edit Unnamed e !! p) s = do
  let (k, s') = fresh s
  done ((Edit (Named k) e ** EditIsNormal) !! p, s', []) -- N-Name
normalise (Edit (Named k) e !! p) s = do
  done ((Edit (Named k) e ** EditIsNormal) !! p, s, []) -- N-Editor
---- Resolve
normalise t@(Repeat t1 !! p) s = do
  ((t1' ** n1') !! p', s', d') <- normalise (assert_smaller t (t1 !! p)) s
  done ((Step t1' (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])) ** StepIsNormal n1') !! p', s', d') -- N-Repeat
  -- normalise (Step t1 (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])) !! p') s <-- Should be equivallent
normalise (Assert b !! p) s =
  done ((Done b ** DoneIsNormal) !! p ++ walk b, s, []) -- N-Assert
-- normalise (Share b !! p) s = do
--   let (l, s') = modify (alloc b) s
--   done ((Done l ** DoneIsNormal) !! p, s')
normalise (Assign v r !! p) s = do
  let s' = modify (write v r) s
  done ((Done (Value ()) ** DoneIsNormal) !! p, s', [Pack r])
normalise _ _ = empty

---- Handling ------------------------------------------------------------------

public export
insert : Editor h (Symbolic b) -> State h -> List (Editor h (Symbolic b), Some Token, State h, Delta h)
insert (Enter) s = do
  let (z, s') = fresh s
  let z' = Fresh b z
  done (Update (Symbol z'), Pack z', s', Prelude.Nil)
insert (Update _) s = do
  let (z, s') = fresh s
  let z' = Fresh b z
  done (Update (Symbol z'), Pack z', s', Prelude.Nil)
insert (Change r) s = do
  let (z, s') = fresh s
  let z' = Fresh b z
  done (Change r, Pack z', modify (write (Symbol z') r) s', [Pack r])
insert (View _) _ = empty
insert (Watch _) _ = empty
insert (Select _) _ = empty

public export
pick : Task h a -> List (Label, Task h a)
pick (Edit n (Select ts)) = [ (l', t')          | (l', t') <- ts, not (failing t') ]
pick (Trans e1 t2)        = [ (l', Trans e1 t') | (l', t') <- pick t2 ]
pick (Step t1 e2)         = [ (l', Step t' e2)  | (l', t') <- pick t1 ]
pick _                    = []

public export
handle : Simulation (Refined (Task h a) IsNormal) -> State h -> List (Simulation (Task h a), Input (Some Token), State h, Delta h)
---- Selections
handle ((Edit (Named k) (Select ts) ** EditIsNormal) !! p) s = do
  (l', t') <- pick (Edit (Named k) (Select ts))
  done (t' !! p, Option (Named k) l', s, []) -- H-Select
---- Editors
handle ((Edit (Named k) e ** EditIsNormal) !! p) s = do
  (e', z', s', d') <- insert e s
  done (Edit (Named k) e' !! p, Insert k z', s', d') -- H-Edit
---- Pass
handle t@((Trans e1 t2 ** TransIsNormal n2) !! p) s = do
  (t2' !! p', i', s', d') <- handle (assert_smaller t ((t2 ** n2) !! p)) s
  done (Trans e1 t2' !! p', i', s', d') -- H-Trans
handle t@((Step t1 e2 ** StepIsNormal n1) !! p) s =
  let fst = do
        (t1' !! p', i', s', d') <- handle (assert_smaller t ((t1 ** n1) !! p)) s -- H-Step
        done (Step t1' e2 !! p', i', s', d')
      snd = case value t1 (get s) of
        Just v1 => do
          (l', t2') <- pick (e2 v1) --XXX: what about p'
          done (t2' !! p, Option Unnamed l', s, []) -- H-Preselect
        Nothing => empty
   in fst <|> snd
handle t@((Pair t1 t2 ** PairIsNormal n1 n2) !! p) s = do
  --KNOW: use the same state!
  (t1' !! p1, i1, s1, d1) <- handle (assert_smaller t ((t1 ** n1) !! p)) s -- H-PairFirst
  (t2' !! p2, i2, s2, d2) <- handle (assert_smaller t ((t2 ** n2) !! p)) s -- H-PairSecond
  done (Pair t1' t2 !! p1, i1, s1, d1) <|> done (Pair t1 t2' !! p2, i2, s2, d2)
handle t@((Choose t1 t2 ** ChooseIsNormal n1 n2) !! p) s = do
  --KNOW: use the same state!
  (t1' !! p1, i1, s1, d1) <- handle (assert_smaller t ((t1 ** n1) !! p)) s -- H-ChooseFirst
  (t2' !! p2, i2, s2, d2) <- handle (assert_smaller t ((t2 ** n2) !! p)) s -- H-ChooseSecond
  done (Choose t1' t2 !! p1, i1, s1, d1) <|> done (Choose t1 t2' !! p2, i2, s2, d2)
---- Rest
handle ((Done _ ** DoneIsNormal) !! p) i = empty
handle ((Fail ** FailIsNormal) !! p) i = empty

---- Fixation ------------------------------------------------------------------

public export
fixate : Simulation (Task h a) -> State h -> Delta h -> List (Simulation (Refined (Task h a) IsNormal), State h)
fixate t s d = do
  ((t' ** n') !! p', s', d') <- normalise t s
  if intersect (d ++ d') (watching t') == []
    then done ((t' ** n') !! p', s')
    else fixate (assert_smaller t (t' !! p')) s' d'

---- Initialisation ------------------------------------------------------------

public export
initialise : Simulation (Task h a) -> State h -> List (Simulation (Refined (Task h a) IsNormal), State h)
initialise t s = fixate t s []

---- Interaction ---------------------------------------------------------------

public export
drive : Simulation (Refined (Task h a) IsNormal) -> State h -> List (Simulation (Refined (Task h a) IsNormal), Input (Some Token), State h)
drive n s = do
  (t', i', s', d') <- handle n s
  (n'', s'') <- fixate t' s' d'
  done (n'', i', s'')

---- Simulation ----------------------------------------------------------------

public export
simulate : Fuel -> Task h a -> State h -> List (List (Input (Some Token)), Simulation a)
simulate us t s = do
  (n', s') <- initialise (final t) s
  (is, v) <- go us n' [] s'
  done (reverse is, v)
  where
    go : Fuel -> Simulation (Refined (Task h a) IsNormal) -> List (Input (Some Token)) -> State h -> List (List (Input (Some Token)), Simulation a)
    go us ((t ** n) !! p) is s with (value t (get s))
      go _          ((t ** n) !! p) is s | Just v  = done (is, v !! p)
      go Dry        ((t ** n) !! p) is s | Nothing = empty -- $ ToFewFuel
      go (More us') ((t ** n) !! p) is s | Nothing = do
        (n' !! p', i', s') <- drive ((t ** n) !! p) s
        go us' (n' !! p') (i' :: is) s'
