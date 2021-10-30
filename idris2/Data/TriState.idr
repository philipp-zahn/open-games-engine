module Data.TriState

public export
data TriState a b = Choice1 a | Choice2 b | Both a b

public export
elimTri : Monoid c => (a -> c) -> (b -> c) -> TriState a b -> c
elimTri f g (Choice1 x) = f x
elimTri f g (Choice2 y) = g y
elimTri f g (Both x y) = f x <+> g y

export
Bifunctor TriState where
  bimap f g (Choice1 a) = Choice1 (f a)
  bimap f g (Choice2 a) = Choice2 (g a)
  bimap f g (Both a b) = Both (f a) (g b)

