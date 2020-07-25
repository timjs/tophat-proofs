module Scratch

import Data.Nat
import Data.Vect

----

data Task : a -> Type where
  Done : a -> Task a
  Bind : Task a' -> (a' -> Task a) -> Task a

total
value : Task a -> Maybe a
value (Done x) = Just x
value (Bind _ _) = Nothing

total
failing : Task a -> Bool
failing (Done x) = False
failing (Bind t c) = failing t

total
normalise : Task a -> Task a
normalise (Done x) = Done x
normalise (Bind t c) = case value t of
  Nothing => Bind t c
  Just v => let t' = c v in if failing t'
    then Bind t c
    -- else normalise (c v)
    else normalise t'

----


reverse : (xs : Vect len elem) -> Vect len elem
reverse xs = go [] xs
  where
    go : (_ : Vect n elem) -> (_ : Vect m elem) -> Vect (n + m) elem
    go         acc []        = rewrite plusZeroRightNeutral n in acc
    go {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m in go (x::acc) xs

-----
{-
sym' : {auto con : Type -> Type} -> {auto inj : (con a = con b) -> (a = b)} -> {p : con a} -> {q : con b} -> (p = q) -> (q = p)
sym' prf = ?sym_rhs

||| Trick: add `con` as an auto implicit helps Idris to fill in the type constructor.
negEqSym' : {auto con : Type -> Type} -> {p : con a} -> {q : con b} -> Not (p = q) -> Not (q = p)
negEqSym' f prf = f (sym' prf)


okays : s -> a -> (s, Either e a)
okays s x = (s, Right x)

throws : s -> e -> (s, Either e a)
throws s e = (s, Left e)

handles : State h -> Task h a -> Input Concrete -> (State h, Either NotApplicable (Task h a))
handles s (Pair t1 t2) i = do
  case handles s t1 i of
    (s', Right t1') => okays s' $ Pair t1' t2 -- H-PairFirst
    (s', Left _) => case handles s' t2 i of
      (s'', Right t2') => okays s'' $ Pair t1 t2'
      (s'', Left e) => throws s'' e
handles s _ i = throws s $ CouldNotHandle i

handleIsPossible : {auto s : State h} -> (t : Task h a) -> (i : Input Concrete) -> IsRight (snd (handles s t i)) -> Elem (dummify i) (inputs t s)
handleIsPossible (Pair t1 t2) i prf with (handles s t1 i)
  handleIsPossible (Pair t1 t2) i prf | (s', Left e) = ?handleIsPossible_rhs_2_rhs_2
  handleIsPossible (Pair t1 t2) i prf | (s', Right t1') = ?handleIsPossible_rhs_2_rhs_3
handleIsPossible t i x = ?handleIsPossible_rhs
    -}
