{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Engine.BayesianGamesNonState
  ( StochasticBayesianOpenGame(..)
  , dependentDecision
  , dependentEpsilonDecision
  , fromLens
  , fromFunctions
  , nature
  , liftStochastic
  , uniformDist
  , distFromList
  , pureAction
  , playDeterministically
  ) where


import           Control.Arrow                      hiding ((+:+))
import           Control.Monad.State                hiding (state)
import           Control.Monad.Trans.Class
import GHC.TypeLits

import Data.Foldable
import           Data.HashMap                       as HM hiding (null,map,mapMaybe)


import Data.List (maximumBy)
import Data.Ord (comparing)
import           Data.Utils
import Numeric.Probability.Distribution.Observable hiding (map, lift, filter)

import Engine.OpenGames hiding (lift)
import Engine.OpticClass
import Engine.TLL
import Engine.Diagnostics

---------------------------------------------
-- Reimplements stateful bayesian from before

type StochasticBayesianOpenGame a b x s y r = OpenGame StochasticOptic StochasticContext a b x s y r

type Agent = String

support :: Constraint0 x => Stochastic x -> [x]
support = map fst . decons

bayes :: (Eq y, Ord x, Ord y) => Stochastic (x, y) -> y -> Stochastic x
bayes a y = mapMaybe (\(x, y') -> if y' == y then Just x else Nothing) a


deviationsInContext :: (Ord y, Show theta)
                    => Double -> Agent -> x -> theta -> Stochastic y -> (y -> Double) -> [y] -> [DiagnosticInfoBayesian x y]
deviationsInContext epsilon name x theta strategy u ys
  = [DiagnosticInfoBayesian { equilibrium = strategicPayoff >= optimalPayoff - epsilon,
                      player = name,
                      payoff = strategicPayoff,
                      optimalMove = optimalPlay,
                      optimalPayoff = optimalPayoff,
                      context = u ,
                      state = x,
                      unobservedState = show theta,
                      strategy = strategy}]
  where strategicPayoff = expected (fmap u strategy)
        (optimalPlay, optimalPayoff) = maximumBy (comparing snd) [(y, u y) | y <- ys]


dependentDecision :: (Eq x, Show x, Ord x, Ord y, Show y) => String -> (x -> [y]) -> StochasticBayesianOpenGame '[Kleisli Stochastic x y] '[[DiagnosticInfoBayesian x y]] x () y Double
dependentDecision name ys = OpenGame {
  play = \(a ::- Nil) -> let v x = do {y <- runKleisli a x; return ((), y)}
                             u () _ = return ()
                            in StochasticOptic v u,
  evaluate = \(a ::- Nil) (StochasticContext h k) ->
     (concat [ let u y = expected (do {t <- (bayes h x);
                                       k t y})
                   strategy = runKleisli a x
                  in deviationsInContext 0 name x theta strategy u (ys x)
              | (theta, x) <- support h]) ::- Nil }

dependentEpsilonDecision :: (Ord x, Eq x, Show x, Ord y, Show y) => Double -> String -> (x -> [y])  -> StochasticBayesianOpenGame '[Kleisli Stochastic x y] '[[DiagnosticInfoBayesian x y]] x () y Double
dependentEpsilonDecision epsilon name ys = OpenGame {
  play = \(a ::- Nil) -> let v x = do {y <- runKleisli a x; return ((), y)}
                             u () _ = return ()
                            in StochasticOptic v u,
  evaluate = \(a ::- Nil) (StochasticContext h k) ->
     (concat [ let u y = expected (do {t <- (bayes h x);
                                       k t y})
                   strategy = runKleisli a x
                  in deviationsInContext epsilon name x theta strategy u (ys x)
              | (theta, x) <- support h]) ::- Nil }



-- Support functionality for constructing open games
fromLens :: (Ord x, Ord s) => (x -> y) -> (x -> r -> s) -> StochasticBayesianOpenGame '[] '[] x s y r
fromLens v u = OpenGame {
  play = \Nil -> StochasticOptic (\x -> return (x, v x)) (\x r -> return (u x r)),
  evaluate = \Nil _ -> Nil}


fromFunctions :: (Ord x, Ord s) => (x -> y) -> (r -> s) -> StochasticBayesianOpenGame '[] '[] x s y r
fromFunctions f g = fromLens f (const g)

nature :: Stochastic x -> StochasticBayesianOpenGame '[] '[] () () x ()
nature a = OpenGame {
  play = \Nil -> StochasticOptic (\() -> do {x <- a; return ((), x)}) (\() () -> return ()),
  evaluate = \Nil _ -> Nil}

liftStochastic :: (Ord x) => (x -> Stochastic y) -> StochasticBayesianOpenGame '[] '[] x () y ()
liftStochastic f = OpenGame {
  play = \Nil -> StochasticOptic (\x -> do {y <- f x; return ((), y)}) (\() () -> return ()),
  evaluate = \_ _ -> Nil}

-- Support functionality for stochastic processes (also interface to the probability module in use)

-- uniform distribution
uniformDist :: (Constraint0 a, Fractional prob) => [a] -> T prob a
uniformDist = uniform

-- tailored distribution from a list
distFromList :: (Constraint0 a, Fractional p, Constraint0 p) => [(a,p)] -> T p a
distFromList = fromFreqs

-- pure action (no randomization)
pureAction x = Kleisli $ const $ certainly x

playDeterministically :: Constraint0 a => a -> Stochastic a
playDeterministically = certainly
