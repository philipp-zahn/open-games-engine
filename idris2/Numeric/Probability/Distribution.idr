module Numeric.Probability.Distribution

export
record T (prob, a : Type) where
  constructor MkProb
  getProb : List (a, prob)

export
(.decons) : T prob a -> List (a, prob)
(.decons) = getProb

export
certainly : Num p => a -> T p a
certainly x = MkProb (pure (x, 1))

export
fromFreqs : (Fractional prob) => List (a,prob) -> T prob a
fromFreqs xs = let q = sum (map snd xs) in MkProb (map (\(x,p) => (x,p/q)) xs)

export
Functor (T p) where
  map f (MkProb ls) = MkProb (map (mapFst f) ls)

export
Num p => Applicative (T p) where
  pure = certainly
  (<*>) (MkProb fs) (MkProb ys) = 
    MkProb [(f x,q*p) | (f,p) <- fs, (x,q) <- ys]

export
Num p => Monad (T p) where
  d >>= f = MkProb [(y,q*p) | (x,p) <- getProb d, (y,q) <- getProb (f x)]

