module Task.Run

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
  | CouldNotChangeVal (Some IsBasic) (Some IsBasic)
  | CouldNotChangeRef (Some IsBasic) (Some IsBasic)
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
normalise : Task h a -> State h -> (Refined (Task h a) IsNormal, State h, Delta h)
---- Step
normalise (Step t1 e2) s =
  let ((t1' ** n1'), s', d') = normalise t1 s
      stay = (Step t1' e2 ** StepIsNormal n1')
   in case value t1' (get s') of
    Nothing => (stay, s', d') -- N-StepNone
    Just v1 =>
      let t2 = e2 v1
       in if failing t2
        then (stay, s', d') -- N-StepFail
        else if not $ isNil $ options t2
          then (stay, s', d') -- N-StepWait
          --> Note that Idris2 can't prove termination when writing `t2` instead of `e2 v1`, see #493
          else
            let (n2', s'', d'') = normalise (e2 v1) s'
             in (n2', s'', d' ++ d'') -- N-StepCont
---- Choose
normalise (Choose t1 t2) s =
  let ((t1' ** n1'), s', d') = normalise t1 s
   in case value t1' (get s') of
    Just _ => ((t1' ** n1'), s', d') -- N-ChooseLeft
    Nothing =>
      let ((t2' ** n2'), s'', d'') = normalise t2 s'
       in case value t2' (get s'') of
        Just _ => ((t2' ** n2'), s'', d' ++ d'') -- N-ChooseRight
        Nothing => ((Choose t1' t2' ** ChooseIsNormal n1' n2'), s'', d' ++ d'') -- N-ChooseNone
---- Converge
normalise (Trans f t2) s =
  let ((t2' ** n2'), s', d') = normalise t2 s
   in ((Trans f t2' ** TransIsNormal n2'), s', d') -- N-Trans
normalise (Pair t1 t2) s =
  let ((t1' ** n1'), s', d')  = normalise t1 s
      ((t2' ** n2'), s'', d'') = normalise t2 s'
   in ((Pair t1' t2' ** PairIsNormal n1' n2'), s'', d' ++ d'') -- N-Pair
---- Ready
normalise (Done x) s =
  ((Done x ** DoneIsNormal), s, []) -- N-Done
normalise (Fail) s =
  ((Fail ** FailIsNormal), s, []) -- N-Fail
---- Name
normalise (Edit Unnamed e) s =
  let (k, s') = fresh s
   in ((Edit (Named k) e ** EditIsNormal), s', []) -- N-Name
normalise (Edit (Named k) e) s =
  ((Edit (Named k) e ** EditIsNormal), s, []) -- N-Editor
---- Resolve
normalise (Test b t1 t2) s =
  if b
    then normalise t1 s
    else normalise t2 s
normalise (Repeat t1) s =
  let ((t1' ** n1'), s', d') = normalise t1 s
   in ((Step t1' (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x])) ** StepIsNormal n1'), s', d') -- N-Repeat
  -- normalise (Step t1 (\x => Edit Unnamed (Select ["Repeat" ~> Repeat t1, "Exit" ~> Done x]))) s <-- Should be equivallent
normalise (Assert p) s =
  ((Done p ** DoneIsNormal), s, []) -- N-Assert
-- normalise (Share b) s =
--   let (l, s') = modify (alloc b) s
--    in ((Done l ** DoneIsNormal), s')
normalise (Assign b l) s =
  let s' = modify (write b l) s
   in ((Done () ** DoneIsNormal), s', [Pack l])

---- Handling ------------------------------------------------------------------

public export
insert : Editor h a -> Concrete -> State h -> Either NotApplicable (Editor h a, State h, Delta h)
insert (Enter @{ok}) (Value @{ok'} v') s with (decBasic ok ok')
  insert (Enter @{ok}) (Value @{ok } v') s | Yes Refl = Right (Update v', s, [])
  insert (Enter @{ok}) (Value @{ok'} v') s | No _ = Left $ CouldNotChangeVal (Pack ok') (Pack ok)
insert (Update @{ok} v) (Value @{ok'} v') s with (decBasic ok ok')
  insert (Update @{ok} v) (Value @{ok } v') s | Yes Refl = Right (Update v', s, [])
  insert (Update @{ok} v) (Value @{ok'} v') s | No _ = Left $ CouldNotChangeVal (Pack ok') (Pack ok)
insert (Change @{ok} v) (Value @{ok'} v') s with (decBasic ok ok')
  insert (Change @{ok} l) (Value @{ok } v') s | Yes Refl = Right (Change l, modify (write v' l) s, [Pack l])
  insert (Change @{ok} l) (Value @{ok'} v') s | No _ = Left $ CouldNotChangeRef (Pack ok') (Pack ok)
insert (View _) c _ = Left $ CouldNotHandleValue c
insert (Watch _) c _ = Left $ CouldNotHandleValue c
insert (Select _) c _ = Left $ CouldNotHandleValue c

public export
pick : Task h a -> Label -> Either NotApplicable (Task h a)
pick t@(Edit n (Select ts)) l =
  case lookup l ts of
    Just t' => do
      if (n, l) `elem` options t
        then Right t'
        else Left $ CouldNotGoTo l
    Nothing => Left $ CouldNotFind l
pick (Trans e1 t2) l =
  case pick t2 l of
    Right t' => Right $ Trans e1 t'
    Left x => Left x
pick (Step t1 e2) l =
  case pick t1 l of
    Right t' => Right $ Step t' e2
    Left x => Left x
pick _ _ = Left $ CouldNotPick

public export
handle : (t : Task h a) -> IsNormal t => Input Concrete -> State h -> Either NotApplicable (Task h a, State h, Delta h)
---- Unnamed
handle (Edit Unnamed e) i s =
  Left $ CouldNotHandle i
---- Selections
handle t@(Edit (Named k) (Select ts)) (Option (Named k') l) s =
  case k ?= k' of
    Yes Refl => case pick t l of
      Right t' => Right (t', s, []) -- H-Select
      Left x => Left x
    No _ => Left $ CouldNotMatch (Named k) (Named k')
handle (Edit (Named k) (Select ts)) i s =
  Left $ CouldNotHandle i
---- Editors
handle (Edit (Named k) e) (Insert k' c) s =
  case k ?= k' of
    Yes Refl => case insert e c s of
      Right (e', s', d') => Right (Edit (Named k) e', s', d') -- H-Edit
      Left x => Left x
    No _ => Left $ CouldNotMatch (Named k) (Named k')
handle (Edit (Named k) e) i s =
  Left $ CouldNotHandle i
---- Pass
handle (Trans e1 t2) @{TransIsNormal n2} i s =
  case handle t2 i s of
    Right (t2', s', d') => Right (Trans e1 t2', s', d') -- H-Trans
    Left x => Left x
handle (Step t1 e2) @{StepIsNormal n1} i s =
  case handle t1 i s of
    Right (t1', s', d') => Right (Step t1' e2, s', d') -- H-Step
    Left _ => case i of
      Option Unnamed l => case value t1 (get s) of
        Just v1 => case pick (e2 v1) l of
          Right t2' => Right (t2', s, []) -- H-Preselect
          Left x => Left x
        Nothing => Left $ CouldNotContinue
      _ => Left $ CouldNotPick
handle (Pair t1 t2) @{PairIsNormal n1 n2} i s =
  case handle t1 i s of
    Right (t1', s', d') => Right (Pair t1' t2, s', d') -- H-PairFirst
    Left _ => case handle t2 i s of
      Right (t2', s', d') => Right (Pair t1 t2', s', d') -- H-PairSecond
      Left x => Left x
handle (Choose t1 t2) @{ChooseIsNormal n1 n2} i s =
  case handle t1 i s of
    Right (t1', s', d') => Right (Choose t1' t2, s', d') -- H-ChooseFirst
    Left _ => case handle t2 i s of
      Right (t2', s', d') => Right (Choose t1 t2', s', d') -- H-ChoosSecond
      Left x => Left x
---- Rest
handle (Done _) i _ = Left $ CouldNotHandle i
handle (Fail) i _ = Left $ CouldNotHandle i

---- Fixation ------------------------------------------------------------------

public export
fixate : Task h a -> State h -> Delta h -> (Refined (Task h a) IsNormal, State h)
fixate t s d =
  let ((t' ** n'), s', d') = normalise t s in
    if intersect (d ++ d') (watching t') == []
      then ((t' ** n'), s')
      else fixate (assert_smaller t t') s' d'

---- Initialisation ------------------------------------------------------------

public export
initialise : Task h a -> State h -> (Refined (Task h a) IsNormal, State h)
initialise t s = fixate t s []

---- Interaction ---------------------------------------------------------------

public export
interact : (t : Task h a) -> IsNormal t => Input Concrete -> State h -> Either NotApplicable (Refined (Task h a) IsNormal, State h)
interact n i s = case handle n i s of
  Left e => Left e
  Right (t', s', d') => Right (fixate t' s' d')

---- Execution -----------------------------------------------------------------

public export
execute : Task h a -> State h -> List (Input Concrete) -> Either NotApplicable (a, State h)
execute t s is =
  let ((t' ** n'), s') = initialise t s in
  go is t' s'
  where
    go : List (Input Concrete) -> (t : Task h a) -> IsNormal t => State h -> Either NotApplicable (a, State h)
    go is t s with (value t (get s))
      go []        t s | Just v  = Right (v, s)
      go []        t s | Nothing = Left $ ToFewInputs
      go is        t s | Just v  = Left $ ToManyInputs is
      go (i :: is) t s | Nothing = do
        ((t' ** n'), s') <- interact t i s
        go is t' s'
