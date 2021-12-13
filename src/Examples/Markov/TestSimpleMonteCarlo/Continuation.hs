{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Examples.Markov.TestSimpleMonteCarlo.Continuation
  ( _sampleDetermineContinuationPayoffsStoch
  , discountFactor
  ) where

import Control.Monad.State ( StateT(StateT), replicateM_ )
import qualified Control.Monad.State as ST
    ( MonadState(put, get), MonadTrans(lift), StateT(runStateT) )
import Data.Utils ( average )
import qualified Data.Vector as V ( fromList )
import Debug.Trace ()
import Engine.Engine
    ( MonadContext(..),
      MonadOptic(..),
      Vector,
      Stochastic,
      List(..),
      OpenGame(evaluate, play),
      (>>>),
      (&&&),
      Kleisli(..),
      distFromList )
import Engine.IOGames
    ( fromFunctions, fromLens, discount, dependentDecisionIO )
import Examples.SimultaneousMoves
    ( ActionPD(..), prisonersDilemmaMatrix )
import Numeric.Probability.Distribution ( decons, certainly )
import Preprocessor.Preprocessor ( opengame )
import System.IO.Unsafe ( unsafePerformIO )
import System.Random.MWC.CondensedTable
    ( CondensedTableV, tableFromProbabilities )

--------------------------------------------------------------------------------
-- Entry points

-- printOutput 20 (transformStratTuple strategyTupleTest) (Cooperate,Cooperate)
-- Own util 1
-- 45.296
-- Other actions
-- [43.957,45.309]
-- Own util 2
-- 44.944
-- Other actions
-- [44.415,45.746]

printOutput
  :: Integer
     -> List
          '[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
            Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
     -> (ActionPD, ActionPD)
     -> IO ()
printOutput iterator strat initialAction = do
  let (result1 ::- result2 ::- Nil) = repeatedPDEq iterator strat initialAction
  (stratUtil1,ys1) <- result1
  (stratUtil2,ys2) <- result2
  putStrLn "Own util 1"
  print stratUtil1
  putStrLn "Other actions"
  print ys1
  putStrLn "Own util 2"

  print stratUtil2
  putStrLn "Other actions"
  print ys2

  where

      repeatedPDEq  iterator strat initialAction =
        evaluate prisonersDilemmaCont strat context
        where context  = contextCont iterator strat initialAction
              -- fix context used for the evaluation
                where contextCont  iterator strat initialAction =
                        MonadContext
                          (pure ((),initialAction))
                          (\_ action -> determineContinuationPayoffsIO
                                          iterator strat action)

strategyTupleTest = stageStrategyTest ::- stageStrategyTest ::- Nil

-- | Classic stochastic definition: equal chance of cooperate/defect.
stageStrategyTest :: Kleisli Stochastic (ActionPD, ActionPD) ActionPD
stageStrategyTest = Kleisli $ const $ distFromList [(Cooperate, 0.5),(Defect, 0.5)]

--------------------------------------------------------------------------------
-- Transforming Stochastic to CondensedTableV

transformStratTuple :: List
                        '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                          Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                    -> List
                        '[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                          Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
transformStratTuple (x ::- y ::- Nil) =
  transformStrat x
  ::- transformStrat y
  ::- Nil

  where
    transformStrat strat = Kleisli (\x ->
      let y = runKleisli strat x
          ls = decons y
          v = V.fromList ls
          in tableFromProbabilities v)

---------------------------------------------
-- Contains a first, very, very shaky version
-- that does Monte Carlo through the evaluate
---------------------------------------------

discountFactor = 1.0

prisonersDilemmaCont :: OpenGame
                          MonadOptic
                          MonadContext
                          ('[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                             Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD])
                          ('[IO (Double,[Double]), IO (Double, [Double])])
                          (ActionPD, ActionPD)
                          ()
                          (ActionPD, ActionPD)
                          ()

prisonersDilemmaCont = [opengame|

   inputs    : (dec1Old,dec2Old) ;
   feedback  :      ;

   :----------------------------:
   inputs    :  (dec1Old,dec2Old)    ;
   feedback  :      ;
   operation : dependentDecisionIO "player1" 100 [Cooperate,Defect];
   outputs   : decisionPlayer1 ;
   returns   : prisonersDilemmaMatrix decisionPlayer1 decisionPlayer2 ;

   inputs    :   (dec1Old,dec2Old)   ;
   feedback  :      ;
   operation : dependentDecisionIO "player2" 100 [Cooperate,Defect];
   outputs   : decisionPlayer2 ;
   returns   : prisonersDilemmaMatrix decisionPlayer2 decisionPlayer1 ;

   operation : discount "player1" (\x -> x * discountFactor) ;

   operation : discount "player2" (\x -> x * discountFactor) ;

   :----------------------------:

   outputs   : (decisionPlayer1,decisionPlayer2)     ;
   returns   :      ;
  |]

--------------------------------
-- This is for the mixed setting
-- which includes the Bayesian setup
-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffs :: Integer
                             -> List
                                      '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                        Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                             -> (ActionPD,ActionPD)
                             -> StateT Vector IO ()
determineContinuationPayoffs 1        strat action = pure ()
determineContinuationPayoffs iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs (pred iterator) strat nextInput
 where executeStrat =  play prisonersDilemmaCont (transformStratTuple strat)


sampleDetermineContinuationPayoffs :: Int
                                  -- ^ Sample size
                                  -> Integer
                                  -- ^ How many rounds are explored?
                                  -> List
                                            '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                              Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                                  -> (ActionPD,ActionPD)
                                  -> StateT Vector IO ()
sampleDetermineContinuationPayoffs sampleSize iterator strat initialValue = do
  replicateM_ sampleSize (determineContinuationPayoffs iterator strat initialValue)
  v <- ST.get
  ST.put (average sampleSize v)

-- NOTE EVIL EVIL
_sampleDetermineContinuationPayoffsStoch :: Int
                                  -- ^ Sample size
                                  -> Integer
                                  -- ^ How many rounds are explored?
                                  -> List
                                            '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                              Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                                  -> (ActionPD,ActionPD)
                                  -> StateT Vector Stochastic ()
_sampleDetermineContinuationPayoffsStoch sampleSize iterator strat initialValue = do
   transformStateTIO $  sampleDetermineContinuationPayoffs sampleSize iterator strat initialValue
   where
      transformStateTIO ::  StateT Vector IO () ->  StateT Vector Stochastic ()
      transformStateTIO sTT = StateT (\s -> unsafeTransformIO $  ST.runStateT sTT s)
      unsafeTransformIO :: IO a -> Stochastic a
      unsafeTransformIO a =
        let a' = unsafePerformIO a
            in certainly a'

-----------------------------
-- For IO only
-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffsIO :: Integer
                               -> List
                                     [Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                                     Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
                               -> (ActionPD,ActionPD)
                               -> StateT Vector IO ()
determineContinuationPayoffsIO 1        strat action = pure ()
determineContinuationPayoffsIO iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffsIO (pred iterator) strat nextInput
 where executeStrat =  play prisonersDilemmaCont strat

----------------------------------------------------
-- This is taken from the other MonteCarloTest setup
-- Needs to be transformed in order to be tested

-- extract continuation
extractContinuation :: MonadOptic s () a () -> s -> StateT Vector IO ()
extractContinuation (MonadOptic v u) x = do
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: MonadOptic s () a () -> s -> IO a
extractNextState (MonadOptic v _) x = do
  (z,a) <- v x
  pure a
