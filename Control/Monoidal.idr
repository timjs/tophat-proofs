-- An alternative formulation of the `Applicative` interface.
module Control.Monoidal

%default total

---- Interface -----------------------------------------------------------------

infixl 6 <&>
infixl 6 <&
infixl 6  &>

public export
interface Functor f => Monoidal f where
  (<&>) : f a -> f b -> f (a, b)
  skip : f ()

public export
(<&) : Monoidal f => f a -> f b -> f a
(<&) x y = map fst (x <&> y)

public export
(&>) : Monoidal f => f a -> f b -> f b
(&>) x y = map snd (x <&> y)

---- Defaults ------------------------------------------------------------------

public export
pureDefault : Monoidal f => a -> f a
pureDefault x = map (const x) skip

public export
applyDefault : Monoidal f => f (a -> b) -> f a -> f b
applyDefault fg fx = map (\(g, x) => g x) (fg <&> fx)

public export
skipDefault : Applicative f => f ()
skipDefault = pure ()

public export
pairDefault : Applicative f => f a -> f b -> f (a, b)
pairDefault fa fb = pure MkPair <*> fa <*> fb

---- Implementations -----------------------------------------------------------

public export
Monoidal Maybe where
  Just x <&> Just y = Just (x, y)
  _      <&> _      = Nothing

  skip = Just ()

-- public export
-- implementation Monoidal (Either e)
