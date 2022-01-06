{-# language DataKinds, TypeOperators, GADTs, MultiParamTypeClasses, KindSignatures, FlexibleInstances, FlexibleContexts, TypeFamilies, FunctionalDependencies, UndecidableInstances, QuasiQuotes, NamedFieldPuns, PartialTypeSignatures, ScopedTypeVariables, GeneralizedNewtypeDeriving , OverloadedStrings, Rank2Types, ConstraintKinds, LambdaCase, RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Examples.Markov.TestSimpleMonteCarlo.Continuation
  ( sampleDetermineContinuationPayoffsStoch
  , discountFactor
  ) where

import           Control.Applicative ( Applicative(liftA2) )
import           Control.Arrow ( Kleisli(runKleisli, Kleisli) )
import           Control.Monad.Reader
import           Control.Monad.State ( StateT(StateT), replicateM_ )
import           Control.Monad.State ( StateT, replicateM, gets, modify, evalStateT )
import qualified Control.Monad.State as ST
    ( MonadState(put, get), MonadTrans(lift), StateT(runStateT) )
import           Control.Monad.Trans.Class as Trans ( MonadTrans(lift) )
import qualified Data.ByteString.Char8 as S8
import           Data.Foldable
import           Data.Functor.Contravariant
import qualified Data.HashMap as HM ( empty, findWithDefault, Map, lookup )
import           Data.IORef
import           Data.Kind ( Type, Constraint )
import           Data.List (maximumBy)
import           Data.Ord
import           Data.Proxy
import           Data.Utils ( adjustOrAdd )
import           Data.Utils ( average )
import qualified Data.Vector as V ( fromList )
import           Debug.Trace ()
import           Engine.IOGames
import           Engine.TLL (traverseList_)
import           GHC.Stack
import           Numeric.Probability.Distribution ( certainly )
import           Numeric.Probability.Distribution ( fromFreqs, T(decons) )
import           Preprocessor.Preprocessor ( opengame )
import qualified RIO
import           RIO (RIO, runRIO, GLogFunc, glog, mkGLogFunc, mapRIO)
import           System.Directory
import           System.IO.Unsafe ( unsafePerformIO )
import           System.Random ( newStdGen )
import           System.Random.MWC.CondensedTable
    ( CondensedTableV, tableFromProbabilities )
import           System.Random.MWC.CondensedTable ( genFromTable, CondensedTableV )
import           System.Random.Stateful ( newIOGenM )
import           Text.Printf



import           Engine.Engine hiding (fromLens,Agent,fromFunctions,discount)
import           Preprocessor.Preprocessor
import           Examples.SimultaneousMoves (ActionPD(..),prisonersDilemmaMatrix)
import           Engine.IOGames
import           Data.Utils

import           Control.Monad.State hiding (state,void)
import qualified Control.Monad.State as ST
import qualified Data.Vector as V
import           Debug.Trace
import           System.IO.Unsafe
import           System.Random.MWC.CondensedTable
import           System.Random
import           System.Random.Stateful
import           Numeric.Probability.Distribution hiding (map, lift, filter)

---------------------------------------------
-- Contains a first, very, very shaky version
-- that does Monte Carlo through the evaluate
---------------------------------------------

---------------------------------------------
-- Types and parameters

type SampleSize = Int


discountFactor = 1.0
---------------------------------------------
-- Game definition

prisonersDilemmaCont :: SampleSize
                     -> SampleSize
                     -> OpenGame
                          (MonadOptic (Msg ActionPD))
                          (MonadContext (Msg ActionPD))
                          ('[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                             Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD])
                          ('[RIO (GLogFunc (Msg ActionPD)) (DiagnosticsMC (ActionPD, ActionPD) ActionPD), RIO (GLogFunc (Msg ActionPD)) (DiagnosticsMC (ActionPD, ActionPD) ActionPD)])
                          (ActionPD, ActionPD)
                          ()
                          (ActionPD, ActionPD)
                          ()

prisonersDilemmaCont sample1 sample2 = [opengame|

   inputs    : (dec1Old,dec2Old) ;
   feedback  :      ;

   :----------------------------:
   inputs    :  (dec1Old,dec2Old)    ;
   feedback  :      ;
   operation : dependentDecisionIO "player1" sample1 [Cooperate,Defect];
   outputs   : decisionPlayer1 ;
   returns   : prisonersDilemmaMatrix decisionPlayer1 decisionPlayer2 ;

   inputs    :   (dec1Old,dec2Old)   ;
   feedback  :      ;
   operation : dependentDecisionIO "player2" sample2 [Cooperate,Defect];
   outputs   : decisionPlayer2 ;
   returns   : prisonersDilemmaMatrix decisionPlayer2 decisionPlayer1 ;

   operation : discount "player1" (\x -> x * discountFactor) ;

   operation : discount "player2" (\x -> x * discountFactor) ;

   :----------------------------:

   outputs   : (decisionPlayer1,decisionPlayer2)     ;
   returns   :      ;
  |]

-- Transform a strategy defined in _Stochastic_ into a probability table
transformStrat :: Kleisli Stochastic x y -> Kleisli CondensedTableV x y
transformStrat strat = Kleisli (\x ->
  let y = runKleisli strat x
      ls = decons y
      v = V.fromList ls
      in tableFromProbabilities v)

-- Transform the strategy tuple from _Stochastic_ into a probability table
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


-- extract continuation
extractContinuation :: MonadOptic (Msg ActionPD) s () a () -> s -> StateT Vector (RIO (GLogFunc (Msg ActionPD))) ()
extractContinuation (MonadOptic v u) x = do
  (z,a) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: MonadOptic (Msg ActionPD) s () a () -> s -> RIO (GLogFunc (Msg ActionPD)) a
extractNextState (MonadOptic v _) x = do
  (z,a) <- v x
  pure a

executeStrat sample1 sample2 strat =  play (prisonersDilemmaCont sample1 sample2) strat

----------------------------------------------------------------------------------------------
-- This is for the mixed setting
-- which includes the Bayesian setup
-- determine continuation for iterator, with the same repeated strategy
-- NOTE this ignores the sample information given in the game definition as it samples only the
-- play independently
determineContinuationPayoffs :: Int
                             -> Int
                             -> Integer
                             -> List
                                      '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                        Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                             -> (ActionPD,ActionPD)
                             -> StateT Vector (RIO (GLogFunc (Msg ActionPD))) ()
determineContinuationPayoffs _ _ 1        strat action = pure ()
determineContinuationPayoffs sample1 sample2 iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs sample1 sample2 (pred iterator) strat nextInput
 where executeStrat =  play (prisonersDilemmaCont sample1 sample2) (transformStratTuple strat)


sampleDetermineContinuationPayoffs :: Int
                                   -- ^ Sample for player 1 - here ignored
                                   -> Int
                                   -- ^ Sample for player 2 - here ignored
                                   ->  Int
                                   -- ^ Sample size
                                   -> Integer
                                   -- ^ How many rounds are explored?
                                   -> List
                                             '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                               Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                                   -> (ActionPD,ActionPD)
                                   -> StateT Vector (RIO (GLogFunc (Msg ActionPD))) ()
sampleDetermineContinuationPayoffs sample1 sample2 sampleSize iterator strat initialValue = do
  replicateM_ sampleSize (determineContinuationPayoffs sample1 sample2 iterator strat initialValue)
  v <- ST.get
  ST.put (average sampleSize v)

-- NOTE EVIL EVIL
sampleDetermineContinuationPayoffsStoch :: GLogFunc (Msg ActionPD)
                                        -> Int
                                        -- ^ Sample size for player 1
                                        -> Int
                                        -- ^ Sample size for player 2
                                        -> Int
                                        -- ^ Sample size
                                        -> Integer
                                        -- ^ How many rounds are explored?
                                        -> List
                                                  '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                                    Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                                        -> (ActionPD,ActionPD)
                                        -> StateT Vector Stochastic ()
sampleDetermineContinuationPayoffsStoch logfunc sample1 sample2 sampleSize iterator strat initialValue = do
   transformStateTIO $  sampleDetermineContinuationPayoffs sample1 sample2 sampleSize iterator strat initialValue
   where
      transformStateTIO ::  StateT Vector (RIO (GLogFunc (Msg ActionPD))) () ->  StateT Vector Stochastic ()
      transformStateTIO sTT = StateT (\s -> unsafeTransformIO $  ST.runStateT sTT s)
      unsafeTransformIO :: RIO (GLogFunc (Msg ActionPD)) a -> Stochastic a
      unsafeTransformIO a =
        let a' = unsafePerformIO (runRIO logfunc a)
            in certainly a'

-----------------------------
-- For IO only
-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffsIO :: Int
                               -- ^ Sample size for player 1
                               -> Int
                               -- ^ Sample size for player 2
                               -> Integer
                               -> List
                                     [Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                                     Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
                               -> (ActionPD,ActionPD)
                               -> StateT Vector (RIO (GLogFunc (Msg ActionPD))) ()
determineContinuationPayoffsIO _ _ 1        strat action = pure ()
determineContinuationPayoffsIO sample1 sample2 iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffsIO sample1 sample2 (pred iterator) strat nextInput
 where executeStrat =  play (prisonersDilemmaCont sample1 sample2) strat

-- fix context used for the evaluation
contextCont sample1 sample2 iterator strat initialAction = MonadContext (pure ((),initialAction)) (\_ action -> determineContinuationPayoffsIO sample1 sample2 iterator strat action)

-- eq definition
repeatedPDEq sample1 sample2 iterator strat initialAction = evaluate (prisonersDilemmaCont sample1 sample2) strat context
  where context  = contextCont sample1 sample2 iterator strat initialAction

-- Prints the information using the logging
printOutput :: Int
            -- ^ Sample size for player 1
            -> Int
            -- ^ Sample size for player 2
            -> Integer
            -> List
                  '[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                    Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
            -> (ActionPD, ActionPD)
            -> IO ()
printOutput sample1 sample2 iterator strat initialAction = do
  indentRef <- newIORef 0
  runRIO (mkGLogFunc logFuncSilent :: GLogFunc (Msg ActionPD)) $ do
    let resultIOs = repeatedPDEq sample1 sample2 iterator strat initialAction
    traverseList_ (Proxy :: Proxy Show) (liftIO . print) resultIOs
    pure ()

----------------------------------------------------
-- Equilibrium analysis
-- Needs to be transformed in order to be tested

-- Add strategy for stage game
stageStrategy :: Kleisli Stochastic (ActionPD, ActionPD) ActionPD
stageStrategy = Kleisli $
   (\case
       (Cooperate,Cooperate) -> playDeterministically Cooperate
       (_,_)         -> playDeterministically Defect)
-- Stage strategy tuple
strategyTuple = stageStrategy ::- stageStrategy ::- Nil

-- Testing for stoch behavior and slow down
stageStrategyTest :: Kleisli Stochastic (ActionPD, ActionPD) ActionPD
stageStrategyTest = Kleisli $ const $ distFromList [(Cooperate, 0.5),(Defect, 0.5)]
-- Stage strategy tuple
strategyTupleTest = stageStrategyTest ::- stageStrategyTest ::- Nil


-- Example usage:
{--
printOutput 100 100  20 (transformStratTuple strategyTupleTest) (Cooperate,Cooperate)
Own util 1
45.296
Other actions
[43.957,45.309]
Own util 2
44.944
Other actions
[44.415,45.746]-}
