{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}



module Examples.Governance.Monitoring
  where

import OpenGames.Engine.Engine
import OpenGames.Preprocessor

import Data.List (delete)
import Numeric.Probability.Distribution (uniform)
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

assignWaterNoTax :: (Double, FarmerMove, MonitorMove) -> (Double, Double)
assignWaterNoTax (startLevel, farmerMove, monitorWorks)
  = case (farmerMove, monitorWorks) of
      (Crack, Work) -> (yield, startLevel - yield)
      (Flood, Work) -> ((1 - punishmentRate)*yield, startLevel - (1 - punishmentRate)*yield)
      (_, Shirk) -> (yield, startLevel - yield)
  where yield = farmerWater startLevel farmerMove
        punishmentRate = 0.65 

randomOrder :: Stochastic (String,String,String)
randomOrder = do
       p1 <- uniform lst
       return (p1,((lst' p1) !! 0),(lst' p1) !! 1)
     where lst = ["farmerA","farmerB","farmerC"]
           lst' x = delete x lst

-- Action spaces
choiceSetFarmer = [Crack, Flood]

choiceSetMonitoring = [Work,Shirk]

-- Payoffs

monitorPayoff :: MonitorMove -> Rational
monitorPayoff Work  = -1
monitorPayoff Shirk = 0

punisher :: FarmerMove -> MonitorMove -> Rational
punisher _ Shirk    = 0
punisher Crack Work = 0
punisher Flood Work = 3

monitorPayoff2 :: Double -> Double -> Double -> MonitorMove -> Double
monitorPayoff2 wage _   c Work  =  wage - c
monitorPayoff2 _    pun c Shirk = - pun


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

-- An irrigation game with three farmers an monitoring; Figure 4C
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

noInput = ()
  
-- Rotating roles
irrigationStepRoleDep =
 [opengame|
   inputs    :  name, startLevel, monitorWorks    ;
   feedback  :     ;

   :----------------------------:
   inputs    : name,noInput    ;
   feedback  :      ;
   operation : dependentRoleDecision (const choiceSetFarmer);
   outputs   : farmerMove ;
   returns   : farmerWater     ;

   inputs    :  startLevel, farmerMove, monitorWorks   ;
   feedback  :      ;
   operation : forwardFunction assignWaterNoTax ;
   outputs   :  farmerWater, downstreamWater;
   returns   :      ;

   :----------------------------:

   outputs   : downstreamWater  ;
   returns   :      ;
  |]



-- An irrigation game with three farmers an monitoring; Figure 4C
irrigationRandomRole = [opengame|
   inputs    :      ;
   feedback  :      ;

   :----------------------------:

   inputs    :  ;
   feedback  :  ;
   operation : nature randomOrder ;
   outputs   : m, p2, p3;
   returns   : ;

   inputs    : (m,noInput) ;
   feedback  :      ;
   operation : dependentRoleDecision  (const choiceSetMonitoring) ;
   outputs   : monitorWorks;
   returns   : monitorPayoff2 0 0 0 monitorWorks;

   inputs    : p2, 10, monitorWorks    ;
   feedback  : monitorWater1    ;
   operation : irrigationStepRoleDep ;
   outputs   : levelAfter1 ;
   returns   : ;

   inputs    : p3, levelAfter1, monitorWorks    ;
   feedback  : monitorWater2    ;
   operation : irrigationStepRoleDep ;
   outputs   : levelAfter2 ;
   returns   : ;

   inputs    : m, levelAfter2, monitorWorks    ;
   feedback  : monitorWater3    ;
   operation : irrigationStepRoleDep ;
   outputs   : levelAfter3 ;
   returns   : ;
   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]



  
-------------
-- Strategies
--

-- stratWork :: Kleisli Stochastic Double FarmerMove
stratWork,stratShirk :: Kleisli Stochastic a MonitorMove
stratWork = pureAction Work
stratShirk = pureAction Shirk

stratCrack,stratFlood :: Kleisli Stochastic a FarmerMove
stratCrack = pureAction Crack
stratFlood = pureAction Flood

stratTupleNoMonitoring =
  stratFlood
  ::- stratFlood
  ::- stratFlood
  ::- Nil

stratTupleNoMonitoring2 =
  stratCrack
  ::- stratFlood
  ::- stratFlood
  ::- Nil

stratTupleMonitoring =
  stratWork
  ::- stratCrack
  ::- stratFlood
  ::- stratFlood
  ::- Nil

stratTupleMonitoring2 =
  stratShirk
  ::- stratFlood
  ::- stratFlood
  ::- stratFlood
  ::- Nil



stratTupleRandomRole =
  stratWork
  ::- stratCrack
  ::- stratCrack
  ::- stratCrack
  ::- Nil

stratTupleRandomRole2 =
  stratWork
  ::- stratCrack
  ::- stratCrack
  ::- stratFlood
  ::- Nil


--------------------
-- equilibrium tests

eqIrrigationNoMonitoring strat = generateIsEq $ evaluate irrigationNoMonitoring strat void

eqIrrigationMonitoring strat =  generateIsEq $ evaluate irrigationMonitoring strat void

eqIrrigationRandom strat = generateIsEq $ evaluate irrigationRandomRole strat void

{-
eqIrrigationNoMonitoring stratTupleNoMonitoring

eqIrrigationRandom stratTupleRandomRole

eqIrrigationRandom stratTupleRandomRole2
-}
