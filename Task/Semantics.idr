module Task.Semantics

import Helpers
import Data.List
import Data.Symbolic
import Task.Syntax
import Task.State
import Task.Observations

-- %default total

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
normalise (Step t1 e2 !! p) s = do
  ((t1' ** n1') !! p', s', d') <- normalise (t1 !! p) s
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
            (n2', s'', d'') <- normalise (t2 !! p') s'
            done (n2', s'', d' ++ d'') -- N-StepCont
---- Choose
normalise (Choose t1 t2 !! p) s = do
  ((t1' ** n1') !! p', s', d') <- normalise (t1 !! p) s
  case value t1' (get s') of
    Just _  => done ((t1' ** n1') !! p', s', d') -- N-ChooseLeft
    Nothing => do
      ((t2' ** n2') !! p'', s'', d'') <- normalise (t2 !! p') s'
      case value t2' (get s'') of
        Just _  => done ((t2' ** n2') !! p'', s'', d' ++ d'') -- N-ChooseRight
        Nothing => done ((Choose t1' t2' ** ChooseIsNormal n1' n2') !! p'', s'', d' ++ d'') -- N-ChooseNone
---- Converge
normalise (Trans f t2 !! p) s = do
  ((t2' ** n2') !! p', s', d') <- normalise (t2 !! p) s
  done ((Trans f t2' ** TransIsNormal n2') !! p', s', d') -- N-Trans
normalise (Pair t1 t2 !! p) s = do
  ((t1' ** n1') !! p' , s' , d' ) <- normalise (t1 !! p ) s
  ((t2' ** n2') !! p'', s'', d'') <- normalise (t2 !! p') s'
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
normalise (Repeat t1 !! p) s = do
  ((t1' ** n1') !! p', s', d') <- normalise (t1 !! p) s
  done ((Step t1' (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])) ** StepIsNormal n1') !! p', s', d') -- N-Repeat
  -- normalise (Step t1 (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])) !! p') s <-- Should be equivallent
normalise (Assert b !! p) s =
  done ((Done b ** DoneIsNormal) !! p ++ b, s, []) -- N-Assert
-- normalise (Share b !! p) s = do
--   let (l, s') = modify (alloc b) s
--   done ((Done l ** DoneIsNormal) !! p, s')
normalise (Assign b l !! p) s = do
  let s' = modify (write b l) s
  done ((Done (Value ()) ** DoneIsNormal) !! p, s', [some l])

---- Handling ------------------------------------------------------------------

public export
insert : Editor h (Symbolic b) -> State h -> List (Editor h (Symbolic b), Some Token, State h, Delta h)
insert (Enter {a=Symbolic b} {ok=SymbolIsBasic ok_b}) s = do
  let (z, s') = fresh s
  let z' = Fresh b z
  done (Update (Symbol z'), some z', s', [])
insert (Update {a=Symbolic b} {ok=SymbolIsBasic ok_b} _) s = do
  let (z, s') = fresh s
  let z' = Fresh b z
  done (Update (Symbol z'), some z', s', [])
insert (Change {a=Symbolic b} {ok=SymbolIsBasic ok_b} l) s = do
  let (z, s') = fresh s
  let z' = Fresh b z
  done (Change l, some z', modify (write (Symbol z') l) s', [some l])
insert (Enter) _ = empty --XXX why needed
insert (Update _) _ = empty --XXX why needed
insert (Change _) _ = empty --XXX why needed
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
handle ((Trans e1 t2 ** TransIsNormal n2) !! p) s = do
  (t2' !! p', i', s', d') <- handle ((t2 ** n2) !! p) s
  done (Trans e1 t2' !! p', i', s', d') -- H-Trans
handle ((Step t1 e2 ** StepIsNormal n1) !! p) s =
  let fst = do
        (t1' !! p', i', s', d') <- handle ((t1 ** n1) !! p) s -- H-Step
        done (Step t1' e2 !! p', i', s', d')
      snd = case value t1 (get s) of
        Just v1 => do
          (l', t2') <- pick (e2 v1) --XXX: what about p'
          done (t2' !! p, Option Unnamed l', s, []) -- H-Preselect
        Nothing => empty
   in fst <|> snd
handle ((Pair t1 t2 ** PairIsNormal n1 n2) !! p) s = do
  --KNOW: use the same state!
  (t1' !! p1, i1, s1, d1) <- handle ((t1 ** n1) !! p) s -- H-PairFirst
  (t2' !! p2, i2, s2, d2) <- handle ((t2 ** n2) !! p) s -- H-PairSecond
  done (Pair t1' t2 !! p1, i1, s1, d1) <|> done (Pair t1 t2' !! p2, i2, s2, d2)
handle ((Choose t1 t2 ** ChooseIsNormal n1 n2) !! p) s = do
  --KNOW: use the same state!
  (t1' !! p1, i1, s1, d1) <- handle ((t1 ** n1) !! p) s -- H-ChooseFirst
  (t2' !! p2, i2, s2, d2) <- handle ((t2 ** n2) !! p) s -- H-ChooseSecond
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
    else fixate ((assert_smaller t t') !! p') s' d'

---- Initialisation ------------------------------------------------------------

public export
initialise : Simulation (Task h a) -> State h -> List (Simulation (Refined (Task h a) IsNormal), State h)
initialise t s = fixate t s []

---- Interaction ---------------------------------------------------------------

public export
interact : Simulation (Refined (Task h a) IsNormal) -> State h -> List (Simulation (Refined (Task h a) IsNormal), Input (Some Token), State h)
interact n s = do
  (t', i', s', d') <- handle n s
  (n'', s'') <- fixate t' s' d'
  done (n'', i', s'')

---- Simulation ----------------------------------------------------------------

{-
public export
execute : Task h a -> State h -> List (Simulation (Symbolic a), List (Input Dummy), State h)
execute t s is =
  let ((t' ** n'), s') = initialise t s in
  go is t' s'
  where
    go : List Input -> (t : Task h a) -> IsNormal t => State h -> List (Either NotApplicable (a, State h))
    go is t s with (value t (get s))
      go []        t s | Just v  = Right (v, s)
      go []        t s | Nothing = Left $ ToFewInputs
      go is        t s | Just v  = Left $ ToManyInputs is
      go (i :: is) t s | Nothing = do
        ((t' ** n'), s') <- interact t i s
        go is t' s'

-}
