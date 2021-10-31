module Numeric.Probability.Distribution

import Data.List
import Data.Map.Interface

record GenericDistribution (m : Type -> Type -> Type) {auto imap : Map m} (prob, a : Type) where
  constructor MkGenDist
  getProb : m a prob


export
T : (prob, a : Type) -> Type
T = GenericDistribution (\a, p => List (a, p))

export
Show p => Show a => Show (T p a) where
  show (MkProb d) = "distribution: \{show d}"

-- Show p => Show a => Interpolation (T p a) where
--   interpolate (MkProb d) = show d
--


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
mapMaybe : (Fractional p) => (a -> Maybe b) -> T p a -> T p b
mapMaybe f =
    fromFreqs . mapMaybe (\(x, p) => (, p) <$> f x) . getProb

export
expected : (Num a) => T a a -> a
expected = sum . map (uncurry (*)) . getProb

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

