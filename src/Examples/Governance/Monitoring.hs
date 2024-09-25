{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}



module Examples.Governance.Monitoring
  where

import OpenGames.Engine.Engine
import OpenGames.Preprocessor


-------------------------------
-- 1 Helper functions and setup
-------------------------------

-- Types

data FarmerMove = Crack | Flood deriving (Eq, Ord, Show)


data MonitorMove = Work | Shirk deriving (Eq, Ord, Show)

-- Payoffs
{-
payoff1 :: FarmerMove -> Rational
payoff1 Crack = 2
payoff1 Flood = 4

payoff2 :: FarmerMove -> FarmerMove -> Rational
payoff2 _ Crack     = 2
payoff2 Flood Flood = 2
payoff2 Crack Flood = 4
-}

farmerWater :: Double -> FarmerMove -> Double
farmerWater startLevel Crack = if startLevel >= 2 then 2 else startLevel
farmerWater startLevel Flood = if startLevel >= 5 then 5 else startLevel


payoffMonitor dec =
  if dec == Work then 1 else 0

-- Helper

assignWater3 :: (Double, FarmerMove, MonitorMove) -> (Double, Double, Double)
assignWater3 (startLevel, farmerMove, monitorWorks)
  = case (farmerMove, monitorWorks) of
      (Crack, Work) -> ((1 - monitorPayRate)*w, monitorPayRate*w, startLevel - w)
      (Flood, Work) -> ((1 - monitorPayRate - punishmentRate)*w, (monitorPayRate + punishmentRate)*w, startLevel - w)
      (_, Shirk) -> (w, 0, startLevel - w)
  where w = farmerWater startLevel farmerMove


-- Action spaces
choiceSetFarmer = [Crack, Flood]

choiceSetMonitoring = [Work,Shirk]

monitorPayoff :: MonitorMove -> Rational
monitorPayoff Work  = -1
monitorPayoff Shirk = 0

punisher :: FarmerMove -> MonitorMove -> Rational
punisher _ Shirk    = 0
punisher Crack Work = 0
punisher Flood Work = 3


-- Parameters

monitorPayRate :: Double
monitorPayRate = 0.2

punishmentRate :: Double
punishmentRate = 0.7

----------
-- 2 Games
----------

-- No monitoring

-- One irrigation step Figure 4A
irrigationStep :: OpenGame
                    StochasticStatefulOptic
                    StochasticStatefulContext
                    '[Kleisli Stochastic Double FarmerMove]
                    '[[DiagnosticInfoBayesian  Double FarmerMove]]
                    (Agent, Double)
                    ()
                    Double
                    ()
irrigationStep = [opengame|
   inputs    :  name, startLevel    ;
   feedback  :      ;

   :----------------------------:
   inputs    : name, startLevel   ;
   feedback  :      ;
   operation : dependentRoleDecision (const choiceSetFarmer);
   outputs   : farmerMove ;
   returns   : farmerWater startLevel farmerMove     ;
   :----------------------------:

   outputs   : startLevel - farmerWater startLevel farmerMove     ;
   returns   :      ;
  |]


-- An irrigation game with three farmers; Figure 4B
irrigationNoMonitoring = [opengame|
   inputs    :      ;
   feedback  :      ;

   :----------------------------:
   inputs    : "farmer1", 10     ;
   feedback  :      ;
   operation : irrigationStep ;
   outputs   : levelAfter1 ;
   returns   : ;

   inputs    : "farmer2",  levelAfter1    ;
   feedback  :      ;
   operation : irrigationStep ;
   outputs   : levelAfter2 ;
   returns   : ;

   inputs    : "farmer3",  levelAfter2    ;
   feedback  :      ;
   operation : irrigationStep ;
   outputs   : levelAfter3 ;
   returns   : ;
   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]


-- External monitor; single step
irrigationStepMonitor3 ::  OpenGame
                              StochasticStatefulOptic
                              StochasticStatefulContext
                              '[Kleisli Stochastic Double FarmerMove]
                              '[[DiagnosticInfoBayesian Double FarmerMove]]
                              (Agent, Double, MonitorMove)
                              Double
                              Double
                              () 
irrigationStepMonitor3 = [opengame|
   inputs    :  name, startLevel, monitorWorks    ;
   feedback  :  monitorWater    ;

   :----------------------------:
   inputs    :  name, startLevel   ;
   feedback  :      ;
   operation : dependentRoleDecision (const choiceSetFarmer);
   outputs   : farmerMove ;
   returns   : farmerWater     ;

   inputs    :  startLevel, farmerMove, monitorWorks   ;
   feedback  :      ;
   operation : forwardFunction assignWater3 ;
   outputs   :  farmerWater, monitorWater, downstreamWater;
   returns   :      ;

   :----------------------------:

   outputs   : downstreamWater  ;
   returns   :      ;
  |]

-- An irrigation game with three farmers; Figure 4B
irrigationMonitoring = [opengame|
   inputs    :      ;
   feedback  :      ;

   :----------------------------:

   inputs    :  ;
   feedback  :      ;
   operation : dependentDecision "monitor" (const choiceSetMonitoring) ;
   outputs   : monitorWorks;
   returns   : monitorWater1 + monitorWater2 + monitorWater3 - (payoffMonitor monitorWorks);

   inputs    : "farmer1", 10, monitorWorks    ;
   feedback  : monitorWater1    ;
   operation : irrigationStepMonitor3 ;
   outputs   : levelAfter1 ;
   returns   : ;

   inputs    : "farmer2", levelAfter1, monitorWorks    ;
   feedback  : monitorWater2    ;
   operation : irrigationStepMonitor3 ;
   outputs   : levelAfter2 ;
   returns   : ;

   inputs    : "farmer3",  levelAfter2, monitorWorks    ;
   feedback  : monitorWater3    ;
   operation : irrigationStepMonitor3 ;
   outputs   : levelAfter3 ;
   returns   : ;
   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]



  {-
-- An irrigation game with three farmers; Figure 4B
irrigationMonitoring = [opengame|
   inputs    :      ;
   feedback  :      ;

   :----------------------------:
   inputs    :  ;
   feedback  :  ;
   operation : irrigationNoMonitoring ;
   outputs   :  ;
   returns   :  ;

   inputs    : "farmer3",  levelAfter2    ;
   feedback  :      ;
   operation : dependentDecision "farmer3" (const choiceSetMonitoring);
   outputs   : monitorDecision ;
   returns   : payoffMonitor monitorDecision;
   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]




  


-- | The same decision in the reduced style, i.e. ignoring empty fields
-- Requires a list of actions, and a payoff function
singleDecisionReduced actionSpace payoffFunction = [opengame|
   operation : dependentDecision "player1" (const actionSpace);
   outputs   : decisionPlayer1 ;
   returns   : payoffFunction decisionPlayer1     ;
  |]



irrigationStep = reindex (\x -> (x, ())) ((reindex (\x -> ((), x)) ((fromFunctions (\x -> x) (\(name, startLevel, farmerMove) -> ())) >>> (reindex (\a1 -> a1) (reindex (\x -> (x, ())) ((reindex (\x -> ((), x)) ((fromFunctions (\(name, startLevel) -> ((name, startLevel), (name, [Crack, Flood], ()))) (\((name, startLevel, farmerMove), ()) -> (name, startLevel, farmerMove))) >>> (reindex (\x -> ((), x)) ((fromFunctions (\x -> x) (\x -> x)) &&& ((dependentDecision)))))) >>> (fromFunctions (\((name, startLevel), farmerMove) -> (name, startLevel, farmerMove)) (\(name, startLevel, farmerMove) -> ((name, startLevel, farmerMove), farmerWater startLevel farmerMove)))))))) >>> (fromLens (\(name, startLevel, farmerMove) -> startLevel - farmerWater startLevel farmerMove) (curry (\((name, startLevel, farmerMove), ()) -> (name, startLevel, farmerMove)))))

irrigationNoMonitoringSrc = Block [] []
  [Line Nothing ["\"farmer1\"", "10"] [] "irrigationStep" ["levelAfter1"] [],
   Line Nothing ["\"farmer2\"", "levelAfter1"] [] "irrigationStep" ["levelAfter2"] [],
   Line Nothing ["\"farmer3\"", "levelAfter2"] [] "irrigationStep" ["levelAfter3"] []]
  [] []
--}
