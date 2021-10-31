module Numeric.Probability.Distribution.Fast

import Data.SortedMap
import Data.FastMap

record T (prob, a : Type) where
  constructor MkProb
  getProb : FastMap a prob

