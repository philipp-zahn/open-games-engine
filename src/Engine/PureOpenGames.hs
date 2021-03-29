{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators, DataKinds, GADTs #-}

module Engine.PureOpenGames where


import Data.List (maximumBy)
import Data.Ord (comparing)
import qualified Optics.Lens as L

import Engine.Diagnostics
import Engine.OpenGames
import Engine.OpticClass
import Engine.TLL

type PureOpenGame a b x s y r = OpenGame PureLens PureLensContext a b x s y r


-- Collect types into meaningful Module
type Agent = String

deviationsInContext :: (Show x, Show y, Ord y)
                    => Double -> Agent -> x -> (x-> y) -> (y -> Double) -> [y] -> [DiagnosticInfoPure x y]
deviationsInContext epsilon name x strategy u ys
  =  [DiagnosticInfoPure {equilibriumP = strategicPayoff >= optimalPayoff - epsilon,
                          playerP = name,
                          optimalMoveP = optimalPlay,
                          strategyP = strategy x,
                          optimalPayoffP = optimalPayoff,
                          payoffP = strategicPayoff,
                          stateP = x
                          }]
  where strategicPayoff = u  $ strategy x
        (optimalPlay, optimalPayoff) = maximumBy (comparing snd) [(y, u y) | y <- ys]




pureDecision :: (Show x, Show y, Ord y) => Agent -> [y] -> PureOpenGame '[x -> y] '[[DiagnosticInfoPure x y]] x () y Double
pureDecision name ys = OpenGame {
  play =  \(a ::- Nil) -> lens (\x -> a x) (\_ _ -> ()),
  evaluate = \(a ::- Nil) (PureLensContext h k) ->
     (concat [ let u  = k
                   strategy =  a
                  in deviationsInContext 0 name h strategy u ys])
                                   ::- Nil }

fromLens :: (x -> y) -> (x -> r -> s) -> PureOpenGame '[] '[] x s y r
fromLens v u = OpenGame {
  play = \Nil -> L.lens v u,
  evaluate = \Nil _ -> Nil}


fromFunctions :: (x -> y) -> (r -> s) -> PureOpenGame '[] '[] x s y r
fromFunctions f g = fromLens f (const g)


