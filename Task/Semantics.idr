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
  | ToFewInputs

---- State ---------------------------------------------------------------------

State : Shape -> Type
State h = (Stream Nat, Heap h)

get : State h -> Heap h
get = snd

modify : (Heap h -> Heap h) -> State h -> State h
modify f (ns, s) = (ns, f s)

fresh : State h -> (Nat, State h)
fresh (n :: ns, s) = (n, (ns, s))

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
normalise (Edit (Named k) e) s
  = ((Edit (Named k) e ** EditIsNormal), s, []) -- N-Editor
---- Resolve
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
   in ((Done () ** DoneIsNormal), s', [some l])

---- Handling ------------------------------------------------------------------

public export
insert : Editor h a -> Concrete -> State h -> Either NotApplicable (Editor h a, State h, Delta h)
insert (Enter {a} {ok}) (Value {a'} {ok'} v') s with (decBasic ok ok')
  insert (Enter {a} {ok}) (Value {a'=a } {ok'=ok } v') s | Yes Refl = Right (Update v', s, [])
  insert (Enter {a} {ok}) (Value {a'=a'} {ok'=ok'} v') s | No _ = Left $ CouldNotChangeVal a' a
insert (Update {a} {ok} v) (Value {a'} {ok'} v') s with (decBasic ok ok')
  insert (Update {a} {ok} v) (Value {a'=a } {ok'=ok } v') s | Yes Refl = Right (Update v', s, [])
  insert (Update {a} {ok} v) (Value {a'=a'} {ok'=ok'} v') s | No _ = Left $ CouldNotChangeVal a' a
insert (Change {a} {ok} v) (Value {a'} {ok'} v') s with (decBasic ok ok')
  insert (Change {a} {ok} l) (Value {a'=a } {ok'=ok } v') s | Yes Refl = Right (Change l, modify (write v' l) s, [some l])
  insert (Change {a} {ok} l) (Value {a'=a'} {ok'=ok'} v') s | No _ = Left $ CouldNotChangeRef a' a
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
handle : Refined (Task h a) IsNormal -> Input Concrete -> State h -> Either NotApplicable (Task h a, State h, Delta h)
---- Unnamed
handle (Edit Unnamed e ** _) i s =
  Left $ CouldNotHandle i
---- Selections
handle (t@(Edit (Named k) (Select ts)) ** _) (Option (Named k') l) s =
  case k ?= k' of
    Yes Refl => case pick t l of
      Right t' => Right (t', s, []) -- H-Select
      Left x => Left x
    No _ => Left $ CouldNotMatch (Named k) (Named k')
handle (Edit (Named k) (Select ts) ** _) i s =
  Left $ CouldNotHandle i
---- Editors
handle (Edit (Named k) e ** _) (Insert k' c) s =
  case k ?= k' of
    Yes Refl => case insert e c s of
      Right (e', s', d') => Right (Edit (Named k) e', s', d') -- H-Edit
      Left x => Left x
    No _ => Left $ CouldNotMatch (Named k) (Named k')
handle (Edit (Named k) e ** _) i s =
  Left $ CouldNotHandle i
---- Pass
handle (Trans e1 t2 ** TransIsNormal n2) i s =
  case handle (t2 ** n2) i s of
    Right (t2', s', d') => Right (Trans e1 t2', s', d') -- H-Trans
    Left x => Left x
handle (Step t1 e2 ** StepIsNormal n1) i s =
  case handle (t1 ** n1) i s of
    Right (t1', s', d') => Right (Step t1' e2, s', d') -- H-Step
    Left _ => case i of
      Option Unnamed l => case value t1 (get s) of
        Just v1 => case pick (e2 v1) l of
          Right t2' => Right (t2', s, []) -- H-Preselect
          Left x => Left x
        Nothing => Left $ CouldNotContinue
      _ => Left $ CouldNotPick
handle (Pair t1 t2 ** PairIsNormal n1 n2) i s =
  case handle (t1 ** n1) i s of
    Right (t1', s', d') => Right (Pair t1' t2, s', d') -- H-PairFirst
    Left _ => case handle (t2 ** n2) i s of
      Right (t2', s', d') => Right (Pair t1 t2', s', d') -- H-PairSecond
      Left x => Left x
handle (Choose t1 t2 ** ChooseIsNormal n1 n2) i s =
  case handle (t1 ** n1) i s of
    Right (t1', s', d') => Right (Choose t1' t2, s', d') -- H-ChooseFirst
    Left _ => case handle (t2 ** n2) i s of
      Right (t2', s', d') => Right (Choose t1 t2', s', d') -- H-ChoosSecond
      Left x => Left x
---- Rest
handle (Done _ ** _) i _ = Left $ CouldNotHandle i
handle (Fail ** _) i _ = Left $ CouldNotHandle i

---- Fixation ------------------------------------------------------------------

fixate : Task h a -> State h -> Delta h -> (Refined (Task h a) IsNormal, State h)
fixate t s d =
  let ((t' ** n'), s', d') = normalise t s in
    if intersect (d ++ d') (watching t') == []
      then ((t' ** n'), s')
      else fixate (assert_smaller t t') s' d'

---- Initialisation ------------------------------------------------------------

initialise : Task h a -> State h -> (Refined (Task h a) IsNormal, State h)
initialise t s = fixate t s []

---- Interaction ---------------------------------------------------------------

interact : Refined (Task h a) IsNormal -> Input Concrete -> State h -> Either NotApplicable (Refined (Task h a) IsNormal, State h)
interact n i s = case handle n i s of
  Left e => Left e
  Right (t', s', d') => Right (fixate t' s' d')

---- Execution -----------------------------------------------------------------

execute : Task h a -> State h -> List (Input Concrete) -> Either NotApplicable (a, State h)
execute t s is =
  let (n', s') = initialise t s in
  go is n' s'
  where
    go : List (Input Concrete) -> Refined (Task h a) IsNormal -> State h -> Either NotApplicable (a, State h)
    go is (t ** n) s = case value t (get s) of
        Just v => Right (v, s)
        Nothing => case is of
          i :: is => interact (t ** n) i s >>= uncurry (go is)
          [] => Left ToFewInputs
