module Task.Observations

import public Control.Monoidal
import Data.List
import Task.Syntax

%default total

---- Values --------------------------------------------------------------------

public export
value' : Editor h a -> State h -> Maybe a
value' (Enter)    _ = Nothing
value' (Update b) _ = Just b
value' (View b)   _ = Just b
value' (Select _) _ = Nothing
value' (Change l) s = Just (read l s)
value' (Watch l)  s = Just (read l s)

public export
value : (t : Task h a) -> IsNormal t => State h -> Maybe a
value (Edit (Named _) e) @{EditIsNormal}         s = value' e s
value (Trans f t1)       @{TransIsNormal n1}     s = map f (value t1 s)
value (Pair t1 t2)       @{PairIsNormal n1 n2}   s = value t1 s <&> value t2 s
value (Done v)           @{DoneIsNormal}         _ = Just v
value (Choose t1 t2)     @{ChooseIsNormal n1 n2} s = value t1 s <|> value t2 s
value (Fail)             @{FailIsNormal}         _ = Nothing
value (Step _ _)         @{StepIsNormal n2}      _ = Nothing

---- Failing -------------------------------------------------------------------

mutual
  public export
  failing' : Editor h a -> Bool
  failing' (Enter)     = False
  failing' (Update _)  = False
  failing' (View _)    = False
  failing' (Select ts) = assert_total $ all (failing . snd) ts
  failing' (Change _)  = False
  failing' (Watch _)   = False

  public export
  failing : Task h a -> Bool
  failing (Edit _ e)     = failing' e
  failing (Trans _ t2)   = failing t2
  failing (Pair t1 t2)   = failing t1 && failing t2
  failing (Done _)       = False
  failing (Choose t1 t2) = failing t1 && failing t2
  failing (Fail)         = True
  failing (Step t1 _)    = failing t1
  failing (Assert _)     = False
  failing (Repeat t1)    = failing t1
  -- failing (Share _)      = False
  failing (Assign _ _)   = False

---- Watching ------------------------------------------------------------------

watching' : Editor h a -> List (t : Type ** Ref h t)
watching' (Enter)        = []
watching' (Update _)     = []
watching' (View _)       = []
watching' (Select _)     = []
watching' (Change {a} l) = [(a ** l)]
watching' (Watch {a} l)  = [(a ** l)]

watching : Task h a -> List (t : Type ** Ref h t)
watching (Edit _ e)     = watching' e
watching (Trans _ t2)   = watching t2
watching (Pair t1 t2)   = watching t1 ++ watching t2
watching (Done _)       = []
watching (Choose t1 t2) = watching t1 ++ watching t2
watching (Fail)         = []
watching (Step t1 _)    = watching t1
watching (Assert _)     = []
watching (Repeat t1)    = watching t1
-- watching (Share _)      = []
watching (Assign _ _)   = []

---- Options -------------------------------------------------------------------

public export
labels : List (Label, Task h a) -> List Label
labels = map fst . filter (not . failing . snd) --> [ l | (l, t) <- _, not (failing t) ] but using this in proofs is tedious

public export
options : Task h a -> List Option
options (Edit n (Select ts)) = map (\l => (n, l)) (labels ts) --> [ (n, l) | l <- labels ts ]
options (Trans _ t2)         = options t2
options (Step t1 _)          = options t1
options (Repeat t1)          = options t1
options (_)                  = []

---- Inputs --------------------------------------------------------------------

public export
inputs' : Editor h a -> List Symbolic
inputs' (Enter {a})    = [Symbol a]
inputs' (Update {a} _) = [Symbol a]
inputs' (View {a} _)   = []
inputs' (Select _)     = [] --> selections do not have `Insert` inputs and are handles separately
inputs' (Change {a} _) = [Symbol a]
inputs' (Watch {a} _)  = []

public export
inputs : (t : Task h a) -> IsNormal t => State h -> List (Input Symbolic)
inputs (Edit (Named n) (Select ts)) @{EditIsNormal}         _ = map (\l => Pick (Named n) l) (labels ts) --> [ (n, Decide l) | l <- labels ts ]
inputs (Edit (Named n) e)           @{EditIsNormal}         s = map (\d => Insert n d) (inputs' e) --> [ (n, Insert d) | d <- inputs' e ]
inputs (Trans _ t2)                 @{TransIsNormal n2}     s = inputs t2 s
inputs (Pair t1 t2)                 @{PairIsNormal n1 n2}   s = inputs t1 s ++ inputs t2 s
inputs (Done _)                     @{DoneIsNormal}         _ = []
inputs (Choose t1 t2)               @{ChooseIsNormal n1 n2} s = inputs t1 s ++ inputs t2 s
inputs (Fail)                       @{FailIsNormal}         _ = []
inputs (Step t1 e2)                 @{StepIsNormal n1}      s = inputs t1 s ++ case value t1 s of
  Nothing => []
  Just v1 => map fromOption (options (e2 v1)) --> [ fromOption o | o <- options (e2 v1) ]
