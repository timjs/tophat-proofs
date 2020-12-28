module Task.Combinators

import Helpers
import Task.Syntax

%default total

---- Instances -----------------------------------------------------------------

Functor (Task h) where
  map = Trans

Monoidal (Task h) where
  skip = Done ()
  (<&>) = Pair

Applicative (Task h) where
  pure = Done
  (<*>) = applyDefault

Alternative (Task h) where
  empty = Fail
  (<|>) = Choose

Monad (Task h) where
  (>>=) = Step

---- Constructors --------------------------------------------------------------

---- Builtins

new : Editor h a -> Task h a
new e = Edit Unnamed e

assert : Bool -> Task h Bool
assert = Assert

---- Editors

enter : IsBasic a => Show a => Task h a
enter = new Enter

update : IsBasic a => Show a => a -> Task h a
update v = new (Update v)

view : IsBasic a => Show a => a -> Task h a
view v = new (View v)

select : List (Label, Task h a) -> Task h a
select ts = new (Select ts)

---- Shares

-- share : IsBasic a => a -> Task h (Ref h a)
-- share = Share

watch : IsBasic a => Show a => Eq a => Ref h a -> Task h a
watch l = new (Watch l)

change : IsBasic a => Show a => Eq a => Ref h a -> Task h a
change l = new (Change l)

infixl 1 <<-
infixl 1 <<=

(<<-) : IsBasic a => Ref h a -> a -> Task h ()
(<<-) = flip Assign

(<<=) : IsBasic a => Show a => Eq a => Ref h a -> (a -> a) -> Task h ()
(<<=) r f = do
  x <- watch r
  r <<- f x

---- Combinators ---------------------------------------------------------------

infixl 3 <?>
infixl 1 >>?
infixl 1 >>*
infixl 1 >**
-- infixl 1 >>@

parallel : List (Task h a) -> Task h (List a)
parallel [] = pure []
parallel (t :: ts) = t <&> parallel ts >>= \(x, xs) => pure (x :: xs)

parallel' : List (Task h a) -> Task h (List a)
parallel' = foldr (\t,res => t <&> res >>= \(x, xs) => pure (x :: xs)) (pure [])

choose : List (Task h a) -> Task h a
choose = foldr (<|>) empty

branch : List (Bool, Task h a) -> Task h a
branch [] = empty
branch ((b, t) :: ts) = Test b t (branch ts)

branch' : List (Bool, Task h a) -> Task h a
branch' = foldr pick empty
  where
    pick : (Bool, Task h a) -> Task h a -> Task h a
    pick (b, t) res = Test b t res

(<?>) : Task h a -> Task h a -> Task h a
(<?>) t1 t2 = select ["Left" ~> t1, "Right" ~> t2]

(>>?) : Task h a -> (a -> Task h b) -> Task h b
(>>?) t1 e2 = t1 >>= \x => select ["Continue" ~> e2 x]

(>>*) : Task h a -> List (Label, a -> Task h b) -> Task h b
(>>*) t1 cs = t1 >>= \x => select (map (\(l, c) => l ~> c x) cs)

(>**) : Task h a -> List (Label, a -> Bool, a -> Task h b) -> Task h b
(>**) t1 cs = t1 >>= \x => select (map (\(l, b, c) => l ~> if b x then c x else empty) cs)

---- Loops ---------------------------------------------------------------------
-- Note that adding below combinators to the task language
-- requires the host language to have recursion!
-- In case of `forever`, normalisation can be non-terminating.
-- In case of `repeat`, the user decides if we're going to repeat or to exit.

covering
forever : Task h a -> Task h Void
forever t1 = t1 >>= \_ => forever t1

covering
repeat : Task h a -> Task h a
repeat t1 = t1 >>= \x => select ["Repeat" ~> repeat t1, "Exit" ~> pure x]

-- covering
-- (>>@) : Task h a -> (a -> Task h b) -> Task h b
-- (>>@) t1 e2 = repeat t1 >>= e2
-- (>>@) t1 e2 = t1 >>= \x => select ["Repeat" ~> t1 >>@ e2, "Exit" ~> e2 x]
