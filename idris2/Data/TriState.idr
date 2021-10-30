module Data.TriState

public export
data TriState a b = One a | Two b | Both a b

public export
elimTri : Monoid c => (a -> c) -> (b -> c) -> TriState a b -> c
elimTri f g (One x) = f x
elimTri f g (Two y) = g y
elimTri f g (Both x y) = f x <+> g y
