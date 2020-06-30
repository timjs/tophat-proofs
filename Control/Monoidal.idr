module Control.Monoidal

infixl 6 <&>
infixl 6 <&
infixl 6 &>

export
interface Applicative f => Monoidal f where
  (<&>) : f a -> f b -> f (a, b)
  (<&>) x y = pure (\x, y => (x, y)) <*> x <*> y

  skip : f ()
  skip = pure ()

  (<&) : f a -> f b -> f a
  (<&) x y = pure fst <*> x <&> y

  (&>) : f a -> f b -> f b
  (&>) x y = pure snd <*> x <&> y

export
implementation Monoidal Maybe

export
implementation Monoidal (Either e)

-- export
-- applyDefault : Monoidal f => f (a -> b) -> f a -> f b
-- applyDefault fg fx = pure (\(g, x) => g x) <*> fg <&> fx

-- export
-- pureDefault : Monoidal f => a -> f a
-- pureDefault x = map (const x) skip
