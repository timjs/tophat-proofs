module Task.Observe

import Helpers
import Task.Syntax
import Task.Input

%default total

---- Values --------------------------------------------------------------------

public export
value' : Editor h a -> Heap h -> Maybe a
value' (Enter)    _ = Nothing
value' (Update b) _ = Just b
value' (View b)   _ = Just b
value' (Change l) s = Just (read l s)
value' (Watch l)  s = Just (read l s)

public export
value : (t : Task h a) -> IsNormal t => Heap h -> Maybe a
value (Edit (Named _) e)     @{EditIsNormal}         s = value' e s
value (Select (Named _) _ _) @{SelectIsNormal _}     _ = Nothing
value (Trans e1 t1)          @{TransIsNormal n1}     s = map e1 (value t1 s)
value (Pair t1 t2)           @{PairIsNormal n1 n2}   s = value t1 s <&> value t2 s
value (Done v)               @{DoneIsNormal}         _ = Just v
value (Choose t1 t2)         @{ChooseIsNormal n1 n2} s = value t1 s <|> value t2 s
value (Fail)                 @{FailIsNormal}         _ = Nothing
value (Step _ _)             @{StepIsNormal _}       _ = Nothing

---- Failing -------------------------------------------------------------------

mutual
  public export
  failing' : Editor h a -> Bool
  failing' (Enter)    = False
  failing' (Update _) = False
  failing' (View _)   = False
  failing' (Change _) = False
  failing' (Watch _)  = False

  public export
  failing : Task h a -> Bool
  failing (Edit _ e)      = failing' e
  failing (Select _ t1 _) = failing t1 --XXX: how about `all (failing . snd) ts`?
  failing (Trans _ t2)    = failing t2
  failing (Pair t1 t2)    = failing t1 && failing t2
  failing (Done _)        = False
  failing (Choose t1 t2)  = failing t1 && failing t2
  failing (Fail)          = True
  failing (Step t1 _)     = failing t1
  failing (Repeat t1)     = failing t1
  failing (Assert _)      = False
  -- failing (Share _)       = False
  failing (Assign _ _)    = False

---- Watching ------------------------------------------------------------------

public export
watching' : Editor h a -> Delta h
watching' (Enter)    = []
watching' (Update _) = []
watching' (View _)   = []
watching' (Change r) = [Pack r]
watching' (Watch r)  = [Pack r]

public export
watching : (t : Task h a) -> IsNormal t => Delta h
watching (Edit _ e)      @{EditIsNormal}         = watching' e
watching (Select _ t1 _) @{SelectIsNormal n1}    = watching t1
watching (Trans _ t2)    @{TransIsNormal n2}     = watching t2
watching (Pair t1 t2)    @{PairIsNormal n1 n2}   = watching t1 ++ watching t2
watching (Done _)        @{DoneIsNormal}         = []
watching (Choose t1 t2)  @{ChooseIsNormal n1 n2} = watching t1 ++ watching t2
watching (Fail)          @{FailIsNormal}         = []
watching (Step t1 _)     @{StepIsNormal n1}      = watching t1

---- Options & Labels ----------------------------------------------------------

-- ||| All *enabled* labels which could be sent to a task.
-- public export
-- possibilities : List (Label, Task h a) -> List Label
-- possibilities = map fst . filter (not . failing . snd) --<< [ l | (l, t) <- _, not (failing t) ] but using this in proofs is tedious

-- public export
-- options : (t : Task h a) -> IsNormal t => List (Id, Label)
-- options (Select (Named k) bs) = map (\l => (k, l)) (possibilities ts) --<< [ (k, l) | l <- possibilities ts ]
-- options (Trans _ t2)         = options t2
-- options (Step t1 _)          = options t1
-- options (_)                  = []

-- ||| All *enabled and disabled* labels which could be sent to a task.
-- public export
-- labels : Task h a -> List Label
-- labels (Edit _ (Select ts)) = map fst ts --<< [ l | (l, _) <- ts ]
-- labels (Trans _ t2)         = labels t2
-- labels (Step t1 _)          = labels t1
-- labels (_)                  = []

---- Interface -----------------------------------------------------------------

public export
ui' : Id -> Editor h a -> Heap h -> String
ui' k (Enter)     _ = "[ ](" ++ show k ++ ")"
ui' k (Update b)  _ = "[ " ++ show b ++ " ](" ++ show k ++ ")"
ui' _ (View b)    _ = "[ " ++ show b ++ " ]"
ui' k (Change r)  s = "[ " ++ show (read r s) ++ " ](" ++ show k ++ ")"
ui' _ (Watch r)   s = "[ " ++ show (read r s) ++ " ]"

ui : (t : Task h a) -> IsNormal t => Heap h -> String
ui (Edit (Named k) e)       @{EditIsNormal}         s = ui' k e s
ui (Select (Named k) t1 bs) @{SelectIsNormal n1}    s = ui t1 s ++ ">>?{ " ++ show (map fst bs) ++ " }(" ++ show k ++ ")"
ui (Trans _ t2)             @{TransIsNormal n2}     s = ui t2 s
ui (Pair t1 t2)             @{PairIsNormal n1 n2}   s = ui t1 s ++ "<&>" ++ ui t2 s
ui (Done _)                 @{DoneIsNormal}         _ = "[ .. ]"
ui (Choose t1 t2)           @{ChooseIsNormal n1 n2} s = ui t1 s ++ "<|>" ++ ui t2 s
ui (Fail)                   @{FailIsNormal}         _ = "fail"
ui (Step t1 e2)             @{StepIsNormal n1}      s = ui t1 s

---- Inputs --------------------------------------------------------------------

public export
inputs' : Id -> Editor h a -> List (Input Abstract)
inputs' k (Enter {a})    = [Insert k (Dummy a)]
inputs' k (Update {a} _) = [Insert k (Dummy a)]
inputs' k (View {a} _)   = []
inputs' k (Change {a} _) = [Insert k (Dummy a)]
inputs' k (Watch {a} _)  = []

public export
inputs : (t : Task h a) -> IsNormal t => Heap h -> List (Input Abstract)
inputs (Edit (Named k) e)       @{EditIsNormal}         s = inputs' k e
inputs (Select (Named k) t1 bs) @{SelectIsNormal n1}    s = case value t1 s of
  Just v1 => [ Pick k l | (l, e) <- bs, not (failing (e v1)) ]
  Nothing => []
inputs (Trans _ t2)             @{TransIsNormal n2}     s = inputs t2 s
inputs (Pair t1 t2)             @{PairIsNormal n1 n2}   s = inputs t1 s ++ inputs t2 s
inputs (Done _)                 @{DoneIsNormal}         _ = []
inputs (Choose t1 t2)           @{ChooseIsNormal n1 n2} s = inputs t1 s ++ inputs t2 s
inputs (Fail)                   @{FailIsNormal}         _ = []
inputs (Step t1 e2)             @{StepIsNormal n1}      s = inputs t1 s
