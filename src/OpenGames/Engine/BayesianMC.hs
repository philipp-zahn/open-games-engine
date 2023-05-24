{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

module OpenGames.Engine.BayesianMC where

import Data.HashMap as HM
import Data.List (nub, maximumBy, sort)
import Data.Ord (comparing)

import Control.Arrow
import Control.Monad.Trans.Class
import Control.Monad.Trans.State hiding (state)

import Control.Monad.Bayes.Class
import Control.Monad.Bayes.Population
import Control.Monad.Bayes.Sampler.Strict

import Data.Utils
import OpenGames.Engine.OpticClass
import OpenGames.Engine.OpenGames hiding (lift)
import OpenGames.Engine.TLL

type Payoff = Double

data StatefulKleisliOptic m s t a b where
    StatefulKleisliOptic :: (s -> m (z, a))
                         -> (z -> b -> StateT Vector m t)
                         -> StatefulKleisliOptic m s t a b

instance (Monad m) => Optic (StatefulKleisliOptic m) where
  lens v u = StatefulKleisliOptic (\s -> return (s, v s)) (\s b -> return (u s b))
  (>>>>) (StatefulKleisliOptic v1 u1) (StatefulKleisliOptic v2 u2) = StatefulKleisliOptic v u
    where v s = do {(z1, a) <- v1 s; (z2, p) <- v2 a; return ((z1, z2), p)}
          u (z1, z2) q = do {b <- u2 z2 q; u1 z1 b}
  (&&&&) (StatefulKleisliOptic v1 u1) (StatefulKleisliOptic v2 u2) = StatefulKleisliOptic v u
    where v (s1, s2) = do {(z1, a1) <- v1 s1; (z2, a2) <- v2 s2; return ((z1, z2), (a1, a2))}
          u (z1, z2) (b1, b2) = do {t1 <- u1 z1 b1; t2 <- u2 z2 b2; return (t1, t2)}
  (++++) (StatefulKleisliOptic v1 u1) (StatefulKleisliOptic v2 u2) = StatefulKleisliOptic v u
    where v (Left s1)  = do {(z1, a1) <- v1 s1; return (Left z1, Left a1)}
          v (Right s2) = do {(z2, a2) <- v2 s2; return (Right z2, Right a2)}
          u (Left z1) b  = u1 z1 b
          u (Right z2) b = u2 z2 b

data StatefulKleisliContext m s t a b where
  StatefulKleisliContext :: m (z, s) 
                         -> (z -> a -> StateT Vector m b) 
                         -> StatefulKleisliContext m s t a b

instance (Monad m) => Precontext (StatefulKleisliContext m) where
  void = StatefulKleisliContext (return ((), ())) (\() () -> return ())

instance (Monad m) => Context (StatefulKleisliContext m) (StatefulKleisliOptic m) where
  cmap (StatefulKleisliOptic v1 u1) (StatefulKleisliOptic v2 u2) (StatefulKleisliContext h k)
            = let h' = do {(z, s) <- h; (_, s') <- v1 s; return (z, s')}
                  k' z a = do {(z', a') <- lift (v2 a); b' <- k z a'; u2 z' b'}
               in StatefulKleisliContext h' k'
  (//) (StatefulKleisliOptic v u) (StatefulKleisliContext h k)
            = let h' = do {(z, (s1, s2)) <- h; return ((z, s1), s2)}
                  k' (z, s1) a2 = do {(_, a1) <- lift (v s1); (_, b2) <- k z (a1, a2); return b2}
               in StatefulKleisliContext h' k'
  (\\) (StatefulKleisliOptic v u) (StatefulKleisliContext h k)
            = let h' = do {(z, (s1, s2)) <- h; return ((z, s2), s1)}
                  k' (z, s2) a1 = do {(_, a2) <- lift (v s2); (b1, _) <- k z (a1, a2); return b1}
               in StatefulKleisliContext h' k'

type StatefulKleisliOpenGame m a b x s y r 
  = OpenGame (StatefulKleisliOptic m) (StatefulKleisliContext m) a b x s y r

type MCIO = Population SamplerIO

mcSupport :: (Eq a, Ord a) => Int -> MCIO a -> IO [a]
mcSupport numParticles a = do xs <- sampleIO 
                                  $ fmap (Prelude.map fst) 
                                  $ explicitPopulation 
                                  $ withParticles numParticles a
                              return (sort $ nub xs)

mcExpectation :: Int -> MCIO Double -> IO Double
mcExpectation numParticles = sampleIO . popAvg id . withParticles numParticles

fromLens :: (Monad m) => (x -> y) -> (x -> r -> s) -> StatefulKleisliOpenGame m '[] '[] x s y r
fromLens v u = OpenGame {
  play = \Nil -> StatefulKleisliOptic (\x -> return (x, v x)) (\x r -> return (u x r)),
  evaluate = \Nil _ -> Nil}

fromFunctions :: (Monad m) => (x -> y) -> (r -> s) -> StatefulKleisliOpenGame m '[] '[] x s y r
fromFunctions f g = fromLens f (const g)

nature :: (Monad m) => m x -> StatefulKleisliOpenGame m '[] '[] () () x ()
nature a = OpenGame {
  play = \Nil -> StatefulKleisliOptic (\() -> do {x <- a; return ((), x)}) (\() () -> return ()),
  evaluate = \Nil _ -> Nil}

data DiagnosticInfoMC x y = DiagnosticInfoMC {
    equilibrium :: Bool
  , player :: String
  , optimalMove :: y
  , strategy :: MCIO y
  , optimalPayoff :: Double
  , context :: y -> MCIO Double
  , payoff :: Double
  , state :: x
  -- , unobservedState :: ?
}

instance Show (DiagnosticInfoMC x y) where
  show DiagnosticInfoMC{..} = "equilibrium \n" ++ (show equilibrium) ++ "\n player \n" ++ (show player) ++ "\n optimalPayoff \n" ++ (show optimalPayoff) ++ "\n payoff \n" ++ (show payoff)

decisionMC :: (Eq x, Ord x) 
           => {- numParticles: -} Int
           -> {- epsilon: -} Double
           -> {- name: -} String
           -> {- options: -} (x -> [y])
           -> StatefulKleisliOpenGame MCIO
                                      '[Kleisli MCIO x y] '[IO [DiagnosticInfoMC x y]] 
                                      x () y Payoff
decisionMC numParticles epsilon name options = OpenGame {
  play = \(a ::- Nil) -> let v x = do {y <- runKleisli a x; return ((), y)}
                             u () r = modify (adjustOrAdd (+ r) r name)
                            in StatefulKleisliOptic v u,
  evaluate = \(a {- :: Kleisli MCIO x y -} ::- Nil) 
              (StatefulKleisliContext h {- MCIO (z, x) -} 
                                      k {- :: z -> y -> StateT Vector MCIO Payoff -}) ->
    let runInState {- :: x -> y -> MCIO Payoff -} x y
          = do { (z, x') <- h;
                 condition (x == x');
                 (r, v) <- runStateT (k z y) HM.empty;
                 return $ r + HM.findWithDefault 0.0 name v
               }
     in do { xs <- mcSupport numParticles (fmap snd h);
             sequence [ do { strategyExpectation <- mcExpectation numParticles (runKleisli a x >>= runInState x);
                             moveExpectations <- sequence [ do { e <- mcExpectation numParticles (runInState x y);
                                                                 return (y, e)
                                                               }
                                                          | y <- options x ];
                             let {(y, ky) = maximumBy (comparing snd) moveExpectations};
                             return $ DiagnosticInfoMC {
                                equilibrium = strategyExpectation >= ky - epsilon,
                                player = name,
                                optimalMove = y,
                                strategy = runKleisli a x,
                                optimalPayoff = ky,
                                context = runInState x,
                                payoff = strategyExpectation,
                                state = x
                             }
                           }
                      | x <- xs]
        } ::- Nil
}
