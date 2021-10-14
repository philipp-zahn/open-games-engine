{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds, MonoLocalBinds #-}

module Numeric.Probability.Distribution.Observable
  ( T
  , decons
  , fromFreqs
  , certainly
  , expected
  , mapMaybe
  , uniform
  , note
  , Constraint0
  ) where

import qualified Control.Monad.ConstrainedNormal as C
import qualified Numeric.Probability.Distribution as O

type Constraint0 a = (Ord a)

class Constraint0 a => Constraint a
instance (Constraint0 a) => Constraint a

newtype T p a = CT { unT :: C.NM Constraint (O.T p) a }
  deriving (Monad, Functor, Applicative)
instance Show (T p a) where show _ = "T p a"

lift :: (Constraint0 a, Num p) => O.T p a -> T p a
lift = CT . C.liftNM

fromFreqs :: (Constraint0 a, Fractional p, Constraint0 p) => [(a,p)] -> T p a
fromFreqs = lift . O.fromFreqs

certainly :: (Constraint0 a, Num p) => a -> T p a
certainly = lift . O.certainly

uniform :: (Constraint0 a, Fractional prob) => [a] -> T prob a
uniform = lift . O.uniform

note :: Applicative m => x -> m ()
note x = pure ()

decons :: (Num p, Fractional p, Constraint0 p, Constraint0 a) => T p a -> [(a,p)]
decons = O.decons . unlift

expected :: (Num a, Fractional a, Constraint0 a) => T a a -> a
expected = O.expected . unlift

mapMaybe ::
     (Constraint0 a, Constraint0 b, Fractional prob)
  => (a -> Maybe b)
  -> T prob a
  -> T prob b
mapMaybe f = lift . O.mapMaybe f . unlift

unlift ::
     forall prob a. (Num prob, Constraint0 a, Fractional prob)
  => T prob a
  -> O.T prob a
unlift = C.lowerNM return (>>=) . unT
