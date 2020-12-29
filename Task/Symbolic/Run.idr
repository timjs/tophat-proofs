module Task.Symbolic.Run

import Helpers
import Data.Fuel
import Data.List
import Data.Symbolic
import Task.Error
import Task.Input
import Task.Symbolic.Syntax
import Task.Symbolic.Observe

%default total

---- Normalisation -------------------------------------------------------------

public export
normalise : Task h a -> Path -> State h -> List (Refined (Task h a) IsNormal, Path, State h, Delta h)
---- Step
normalise (Step t1 e2) p s = do
  ((t1' ** n1'), p', s', d') <- normalise t1 p s
  let stay = (Step t1' e2 ** StepIsNormal n1')
  case value t1' (get s') of
    Nothing => done (stay, p', s', d') -- N-StepNone
    Just v1 => do
      let t2 = e2 v1
      if failing t2
        then done (stay, p', s', d') -- N-StepFail
        else do
          --NOTE: Idris2 can't prove termination when writing `t2` instead of `e2 v1`, see #493
          (n2', p'', s'', d'') <- normalise (e2 v1) p' s'
          done (n2', p'', s'', d' ++ d'') -- N-StepCont
---- Choose
normalise (Choose t1 t2) p s = do
  ((t1' ** n1'), p', s', d') <- normalise t1 p s
  case value t1' (get s') of
    Just _  => done ((t1' ** n1'), p', s', d') -- N-ChooseLeft
    Nothing => do
      ((t2' ** n2'), p'', s'', d'') <- normalise t2 p' s'
      case value t2' (get s'') of
        Just _  => done ((t2' ** n2'), p'', s'', d' ++ d'') -- N-ChooseRight
        Nothing => done ((Choose t1' t2' ** ChooseIsNormal n1' n2'), p'', s'', d' ++ d'') -- N-ChooseNone
---- Select
normalise (Select Unnamed t1 bs) p s = do
  ((t1' ** n1'), p', s', d') <- normalise t1 p s
  let (k, s'') = fresh s'
  done ((Select (Named k) t1' bs ** SelectIsNormal n1'), p', s'', d')
normalise (Select (Named k) t1 bs) p s = do
  ((t1' ** n1'), p', s', d') <- normalise t1 p s
  done ((Select (Named k) t1' bs ** SelectIsNormal n1'), p', s', d')
---- Converge
normalise (Trans f t2) p s = do
  ((t2' ** n2'), p', s', d') <- normalise t2 p s
  done ((Trans f t2' ** TransIsNormal n2'), p', s', d') -- N-Trans
normalise (Pair t1 t2) p s = do
  ((t1' ** n1'), p' , s' , d' ) <- normalise t1 p  s
  ((t2' ** n2'), p'', s'', d'') <- normalise t2 p' s'
  done ((Pair t1' t2' ** PairIsNormal n1' n2'), p'', s'', d' ++ d'') -- N-Pair
---- Ready
normalise (Done x) p s =
  done ((Done x ** DoneIsNormal), p, s, []) -- N-Done
normalise (Fail) p s =
  done ((Fail ** FailIsNormal), p, s, []) -- N-Fail
---- Name
normalise (Edit Unnamed e) p s = do
  let (k, s') = fresh s
  done ((Edit (Named k) e ** EditIsNormal), p, s', []) -- N-Name
normalise (Edit (Named k) e) p s = do
  done ((Edit (Named k) e ** EditIsNormal), p, s, []) -- N-Editor
---- Resolve
normalise (Test b t1 t2) p s =
  let fst = do
        (n1', p1', s', d') <- normalise t1 p s
        done (n1', p1' ++ walk b, s', d')
      snd = do
        (n2', p2', s', d') <- normalise t2 p s
        done (n2', p2' ++ walk (Not b), s', d')
   in fst <|> snd
normalise (Repeat t1) p s = do
  ((t1' ** n1'), p', s', d') <- normalise t1 p s
  let (k, s'') = fresh s'
  done ((Select (Named k) t1' ["Repeat" ~> \_ => Repeat t1, "Exit" ~> \x => Done x] ** SelectIsNormal n1'), p', s'', d') -- N-Repeat
normalise (Assert b) p s =
  done ((Done b ** DoneIsNormal), p ++ walk b, s, []) -- N-Assert
-- normalise (Share b) p s = do
--   let (l, s') = modify (alloc b) s
--   done ((Done l ** DoneIsNormal), p, s')
normalise (Assign v r) p s = do
  let s' = modify (write v r) s
  done ((Done (Value ()) ** DoneIsNormal), p, s', [Pack r])

---- Handling ------------------------------------------------------------------

public export
insert : Editor h (Symbolic a) -> State h -> List (Editor h (Symbolic a), Some Token, State h, Delta h)
insert (Enter) s = do
  let (z, s') = fresh s
  let z' = Fresh a z
  done (Update (Symbol z'), Pack z', s', Prelude.Nil)
insert (Update _) s = do
  let (z, s') = fresh s
  let z' = Fresh a z
  done (Update (Symbol z'), Pack z', s', Prelude.Nil)
insert (Change r) s = do
  let (z, s') = fresh s
  let z' = Fresh a z
  done (Change r, Pack z', modify (write (Symbol z') r) s', [Pack r])
insert (View _) _ = empty
insert (Watch _) _ = empty

-- public export
-- pick : Task h a -> List (Label, Task h a)
-- pick (Edit n (Select ts)) = [ (l', t')          | (l', t') <- ts, not (failing t') ]
-- pick (Trans e1 t2)        = [ (l', Trans e1 t') | (l', t') <- pick t2 ]
-- pick (Step t1 e2)         = [ (l', Step t' e2)  | (l', t') <- pick t1 ]
-- pick _                    = []

public export
handle : (t : Task h a) -> IsNormal t => Path -> State h -> List (Task h a, Path, Input (Some Token), State h, Delta h)
---- Selections
handle (Select (Named k) t1 bs) @{SelectIsNormal n1} p s =
  let fst = case value t1 (get s) of
        Nothing => empty
        Just v1 => do
          (l, e) <- bs
          let t' = e v1
          guard $ not (failing t')
          done (t', p, Pick k l, s, []) -- H-Select
      snd = do
        (t1', p', i', s', d') <- handle t1 p s
        done (Select (Named k) t1' bs, p', i', s', d')
  in fst <|> snd
---- Editors
handle (Edit (Named k) e) p s = do
  (e', z', s', d') <- insert e s
  done (Edit (Named k) e', p, Insert k z', s', d') -- H-Edit
---- Pass
handle (Trans e1 t2) @{TransIsNormal n2} p s = do
  (t2', p', i', s', d') <- handle t2 p s
  done (Trans e1 t2', p', i', s', d') -- H-Trans
handle (Step t1 e2) @{StepIsNormal n1} p s = do
  (t1', p', i', s', d') <- handle t1 p s -- H-Step
  done (Step t1' e2, p', i', s', d')
handle (Pair t1 t2) @{PairIsNormal n1 n2} p s =
  --NOTE: use the same state!
  let fst = do
        (t1', p1, i1, s1, d1) <- handle t1 p s -- H-PairFirst
        done (Pair t1' t2, p1, i1, s1, d1)
      snd = do
        (t2', p2, i2, s2, d2) <- handle t2 p s -- H-PairSecond
        done (Pair t1 t2', p2, i2, s2, d2)
   in fst <|> snd
handle (Choose t1 t2) @{ChooseIsNormal n1 n2} p s =
  --NOTE: use the same state!
  let fst = do
        (t1', p1, i1, s1, d1) <- handle t1 p s -- H-ChooseFirst
        done (Choose t1' t2, p1, i1, s1, d1)
      snd = do
        (t2', p2, i2, s2, d2) <- handle t2 p s -- H-ChooseSecond
        done (Choose t1 t2', p2, i2, s2, d2)
   in fst <|> snd
---- Rest
handle (Done _) _ _ = empty
handle (Fail) _ _ = empty

---- Fixation ------------------------------------------------------------------

public export
fixate : Task h a -> Path -> State h -> Delta h -> List (Refined (Task h a) IsNormal, Path, State h)
fixate t p s d = do
  ((t' ** n'), p', s', d') <- normalise t p s
  if intersect (d ++ d') (watching t') == []
    then done ((t' ** n'), p', s')
    else fixate (assert_smaller t t') p' s' d'

---- Initialisation ------------------------------------------------------------

public export
initialise : Task h a -> Path -> State h -> List (Refined (Task h a) IsNormal, Path, State h)
initialise t p s = fixate t p s []

---- Interaction ---------------------------------------------------------------

public export
interact : (t : Task h a) -> IsNormal t => Path -> State h -> List (Refined (Task h a) IsNormal, Path, Input (Some Token), State h)
interact t p s = do
  (t', p', i', s', d') <- handle t p s
  (n'', p'', s'') <- fixate t' p' s' d'
  done (n'', p'', i', s'')

---- Simulation ----------------------------------------------------------------

public export
simulate : Fuel -> Task h a -> State h -> List (List (Input (Some Token)), Path, a)
simulate us t s = do
  ((t' ** n'), p', s') <- initialise t start s
  (is, p, v) <- go us t' p' [] s'
  done (reverse is, p, v)
  where
    go : Fuel -> (t : Task h a) -> IsNormal t => Path -> List (Input (Some Token)) -> State h -> List (List (Input (Some Token)), Path, a)
    go us t p is s with (value t (get s))
      go _          t p is s | Just v  = done (is, p, v)
      go Dry        t p is s | Nothing = empty -- $ ToFewFuel
      go (More us') t p is s | Nothing = do
        ((t' ** n'), p', i', s') <- interact t p s
        go us' t' p' (i' :: is) s'

---- Hints ---------------------------------------------------------------------

export
partial -- Due to pattern match on input list, but we know it has elements :-P
hints : Fuel -> Task h (Symbolic a) -> State h -> (Symbolic a -> Symbolic Bool) -> List (Input (Some Token), Path)
hints Dry       t s g = []
hints (More us) t s g = [ (i, p') | (i :: is, p, v) <- simulate us t s, let p' = p ++ walk (g v), satisfiable p' ]
