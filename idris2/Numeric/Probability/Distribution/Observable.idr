module Numeric.Probability.Distribution.Observable

export
data T : (p, a : Type) -> Type where
  FromFreqs : Fractional p => List (a,p) -> T p ab
  Certainly :  a -> T p a
  MapMaybe : Fractional prob =>  (a -> Maybe b) -> T prob a -> T prob b
  Uniform : Fractional prob =>  List a -> T prob a
  Bind : T p x -> (x -> T p b) -> T p b
  Note :  String -> T p ()
  Norm : Ord x => T p x -> T p x

export
implementation (Num prob, Ord prob, Show prob, Ord a, Show a) => Show (T prob a) where
  show _ = "T"

export
implementation Num prob => Functor (T prob) where
  map f p = Bind p (Certainly . f)
  
export
implementation Num prob => Applicative (T prob) where
  pure = Certainly 
  (<*>) f x = Bind f (\fn => Bind x (Certainly . fn))

export
implementation (Num prob) => Monad (T prob) where
  (>>=) = Bind

--------------------------------------------------------------------------------
-- Interpetable

-- fromFreqs : (Fractional p, HasCallStack) => [(a,p)] -> T p a
-- fromFreqs = FromFreqs callStack
-- 
-- certainly : HasCallStack => a -> T p a
-- certainly = Certainly callStack
-- 
-- mapMaybe :
--      (Fractional prob, HasCallStack) => (a -> Maybe b) -> T prob a -> T prob b
-- mapMaybe = MapMaybe callStack
-- 
-- uniform : (Fractional prob, HasCallStack) => [a] -> T prob a
-- uniform = Uniform callStack
-- 
-- note : HasCallStack => String -> T prob ()
-- note = Note callStack
-- 
-- norm : Ord x => T p x -> T p x
-- norm = Norm

--------------------------------------------------------------------------------
-- Exports; this is where the monad is "run" and where we can
-- reasonably print a trace.
-- 
-- decons : (Num p, Fractional p) => T p a -> [(a,p)]
-- decons t = unsafePerformIO (observeT t)
-- 
-- expected : (Num a, Fractional a) => T a a -> a
-- expected = sum . List.map (\(x,p) -> x * p) . decons
