module Engine.BayesianGames

import Data.List 
import Data.Maybe
import Data.Morphisms
import Data.TLL
import Data.SortedMap

import Engine.OpenGames 
import Engine.OpticClass
import Engine.Diagnostics

import Control.Arrow
import Control.Monad.State

---------------------------------------------
-- Reimplements stateful bayesian from before

StochasticStatefulBayesianOpenGame : (a : List Type) -> (x, s, y, r : Type) 
    -> (b : TypeList a -> StochasticStatefulContext x s y r -> List Type) -> Type
StochasticStatefulBayesianOpenGame a x s y r b = OpenGame StochasticStatefulOptic StochasticStatefulContext a x s y r b

Agent : Type
Agent = String

support : Stochastic x -> List x
support = map fst . (.decons)

bayes : (Eq y) => Stochastic (x, y) -> y -> Stochastic x
bayes a y = mapMaybe (\(x, y') => if y' == y then Just x else Nothing) a


maximumBy : Foldable t => (a -> a -> Ordering) -> t a -> a
maximumBy cmp = fromMaybe ?fail
  . foldl max' Nothing
  where
    max' : Maybe a -> a -> Maybe a
    max' mx y = Just $ case mx of
      Nothing => y
      Just x => case cmp x y of
        GT => x
        _ => y

deviationsInContext : (Show theta) => -- (Show x, Show y, Ord y, Show theta) =>
                     Double -> Agent -> x -> theta -> Stochastic y -> (y -> Double) -> List y -> List (DiagnosticInfoBayesian x y)
deviationsInContext epsilon name x theta strategy u ys =
  let strategicPayoff = expected (map u strategy)
      (optimalPlay, optimalPayoff) = maximumBy (comparing snd) [(y, u y) | y <- ys]
  in  [MkDiagnosticInfoBayesian { equilibrium = strategicPayoff >= optimalPayoff - epsilon
                                , player = name
                                , optimalMove = optimalPlay
                                , strategy = strategy
                                , optimalPayoff = optimalPayoff
                                , context = u 
                                , payoff = strategicPayoff
                                , state = x
                                , unobservedState = show theta
                                }
                                ]


findDeviations : (Show theta) => Double -> Agent -> x -> theta -> Kleislimorphism (T Double) x y -> List y
              -> List (DiagnosticInfoBayesian x y)
findDeviations epsilon name x theta st res = deviationsInContext epsilon name x theta strategy expected res
  where
    strategy : Stochastic y
    strategy = applyKleisli st x
    expected : y -> Double
    expected v = expected ((?implSd))

dependentDecision : (Eq x, Show x, Ord y, Show y) 
                  => String 
                  -> (x -> List y) 
                  -> StochasticStatefulBayesianOpenGame [Kleislimorphism Stochastic x y] x () y Double 
                                                        (\_, _ => [List (DiagnosticInfoBayesian x y)])
dependentDecision name ys = MkGame 
  (\[a] => MkStochasticStatefulOptic 
             (\arg => do {y <- applyKleisli a arg; pure ((), y)})
             (\(), r => do { v <- get ; put (\name' => if name == name' then v name' + r else v name')}))
  (\[a], (MkStochasticStatefulContext h k ) => 
      [concat {t=List} [ findDeviations 0 name x theta a (ys x) | (theta, x) <- support h]])

{-

dependentEpsilonDecision : (Eq x, Show x, Ord y, Show y) 
    => Double -> String -> (x -> [y])  
    -> StochasticStatefulBayesianOpenGame '[Kleisli Stochastic x y] x () y Double 
                                          (KonstSym0 @@ '[[DiagnosticInfoBayesian x y]] )
dependentEpsilonDecision epsilon name ys = OpenGame
  (\(a :- Nil) -> let v x = do {y <- runKleisli a x; return ((), y)}
                       u () r = do {v <- get; put (\name' -> if name == name' then v name' + r else v name')}
                    in StochasticStatefulOptic v u)
  (\(a :- Nil)  v -> undefined)
--  (\(a :- Nil) (StochasticStatefulContext h k) ->
--     (concat [ let u y = expected (evalStateT (do {t <- lift (bayes h x); r <- k t y; v <- get; return (r + v name)}) (const 0))
--                   strategy = runKleisli a x
--                  in deviationsInContext epsilon name x theta strategy u (ys x)
--              | (theta, x) <- support h]) :- Nil )

-- Support functionality for constructing open games
fromLens : (x -> y) -> (x -> r -> s) -> StochasticStatefulBayesianOpenGame '[] x s y r (KonstSym0 @@ '[])
fromLens v u = OpenGame
  (\Nil -> StochasticStatefulOptic (\x -> return (x, v x)) (\x r -> return (u x r)))
  (\Nil _ -> Nil)

nature : Stochastic x -> StochasticStatefulBayesianOpenGame '[] () () x () (KonstSym0 @@ '[])
nature a = OpenGame 
  (\Nil -> StochasticStatefulOptic (\() -> do {x <- a; return ((), x)}) (\() () -> return ()))
  (\Nil _ -> Nil)

liftStochastic : (x -> Stochastic y) -> StochasticStatefulBayesianOpenGame '[] x () y () (KonstSym0 @@ '[])
liftStochastic f = OpenGame 
  (\Nil -> StochasticStatefulOptic (\x -> do {y <- f x; return ((), y)}) (\() () -> return ()))
  (\_ _ -> Nil)

-- Support functionality for stochastic processes (also interface to the probability module in use)

-- uniform distribution
uniformDist = uniform

-- tailored distribution from a list
distFromList = fromFreqs

-- pure action (no randomization)
pureAction x = Kleisli $ const $ certainly x

playDeterministically : a -> Stochastic a
playDeterministically = certainly
{-
-}
