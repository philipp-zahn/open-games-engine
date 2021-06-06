{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Examples.Consensus.AndGate where

import Numeric.Probability.Distribution (certainly, uniform, fromFreqs)

import Engine.BayesianGames
import Engine.OpticClass
import Engine.BayesianGames
import Engine.OpenGames
import Engine.TLL
import Engine.Vec
import Engine.Nat
import Preprocessor.Compile
import Prelude hiding (replicate, map)

obfuscateAndGate :: [Bool] -> Bool
obfuscateAndGate = and

payoffAndGate :: Double -> Double -> [Double] -> Bool -> [Double]
payoffAndGate penalty reward deposits True
  | (sumDeposits > 0) = [deposit*reward/sumDeposits | deposit <- deposits]
  | (sumDeposits == 0) = [0 | _ <- deposits]
  where sumDeposits = sum deposits
payoffAndGate penalty reward deposits False
  = [-penalty*deposit | deposit <- deposits]

unit = ()

depositStagePlayer name minDeposit maxDeposit incrementDeposit epsilon = [opengame|
  inputs : costOfCapital ;
  :---------------------:

  inputs : costOfCapital ;
  feedback : ;
  operation : dependentEpsilonDecision epsilon name (const [minDeposit, minDeposit + incrementDeposit .. maxDeposit]) ;
  outputs : deposit ;
  returns : (-deposit) * costOfCapital ;

  :---------------------:
  outputs : deposit ;

  |]

playingStagePlayer name moves = [opengame|
  inputs : observation, bribe ;
  feedback : ;
  :---------------------:

  inputs : observation, bribe ;
  feedback : ;
  operation : dependentDecision name (const moves) ;
  outputs : move ;
  returns : payoff + if bribePaid then bribe else 0 ;

  :---------------------:
  outputs : move ;
  returns : payoff, bribePaid ;
  |]

attackerPayoff :: [Bool] -> Double -> Double -> Double
attackerPayoff bribesAccepted bribe successfulAttackPayoff
  | (numBribed == numPlayers) = successfulAttackPayoff - bribe*(fromIntegral numBribed)
  | (otherwise)               = -bribe*(fromIntegral numBribed)
  where numPlayers = length bribesAccepted
        numBribed  = length (filter id bribesAccepted)

successfulAttackPayoffDistribution :: Double -> Double -> Stochastic Double
successfulAttackPayoffDistribution attackerProbability maxSuccessfulAttackPayoff
  | (attackerProbability == 0) = certainly 0
  | (attackerProbability == 1) = certainly maxSuccessfulAttackPayoff
  | (otherwise) = fromFreqs [(0, 1-attackerProbability), (maxSuccessfulAttackPayoff, attackerProbability)]

andGateGame numPlayers@(Succ n) (reward :: Double) costOfCapital
            minBribe maxBribe incrementBribe
            maxSuccessfulAttackPayoff attackerProbability penalty
            minDeposit maxDeposit incrementDeposit
            epsilon =
              let mkDepositer = \n -> depositStagePlayer ("Player " ++ show n) minDeposit maxDeposit incrementDeposit epsilon
                  mkPlayer = (\n -> playingStagePlayer ("Player " ++ show n) [True, False])
                  pop = \fn -> population n (map fn (enumerate numPlayers)) in
                  [opengame|
  inputs : replicate numPlayers costOfCapital ;
  feedback : discard1 ;
  operation : pop mkDepositer ;
  outputs : deposits ;
  returns : replicate numPlayers unit ;

  operation : nature (successfulAttackPayoffDistribution attackerProbability maxSuccessfulAttackPayoff) ;
  outputs : successfulAttackPayoff ;

  inputs : deposits, successfulAttackPayoff ;
  operation : dependentDecision "Attacker" (const [minBribe, minBribe+incrementBribe .. maxBribe]) ;
  outputs : bribe ;
  returns : attackerPayoff bribesAccepted bribe successfulAttackPayoff ;

  inputs : (replicate numPlayers (deposits, bribe)) ;
  feedback : discard2 ;
  operation : pop mkPlayer ;
  outputs : moves ;
  returns : _ ; --zip (payoffAndGate penalty reward deposits (obfuscateAndGate moves)) bribesAccepted ;

  inputs : moves ;
  operation : fromFunctions (map not) id ;
  outputs : bribesAccepted ;
|]
