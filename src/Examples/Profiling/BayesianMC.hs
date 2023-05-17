{-# LANGUAGE QuasiQuotes #-}

module Examples.Profiling.BayesianMC where

-- New backend
import Control.Arrow (Kleisli (..))
import Control.Monad.Bayes.Class

import OpenGames.Engine.OpticClass
import OpenGames.Engine.OpenGames
import OpenGames.Engine.BayesianMC
import OpenGames.Engine.TLL
import OpenGames.Engine.Diagnostics
import OpenGames.Preprocessor


particles = 1000 :: Int
epsilon = 0.1 :: Double

s :: (Monad m) => Kleisli m Int Int
s = Kleisli pure

coordinate :: Int -> Int -> Double
coordinate x y = - fromIntegral (abs (x - y))



profiling_game = [opengame|
  inputs: ;
  :-----:

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x1 ;

  inputs : x1 ;
  operation : decisionMC particles epsilon "p1" (const [1 .. 10]) ;
  outputs : y1 ;
  returns : coordinate x1 y1 ;

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x2 ;

  inputs : x2 ;
  operation : decisionMC particles epsilon "p2" (const [1 .. 10]) ;
  outputs : y2 ;
  returns : coordinate x2 y2 ;

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x3 ;

  inputs : x3 ;
  operation : decisionMC particles epsilon "p3" (const [1 .. 10]) ;
  outputs : y3 ;
  returns : coordinate x3 y3 ;

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x4 ;

  inputs : x4 ;
  operation : decisionMC particles epsilon "p4" (const [1 .. 10]) ;
  outputs : y4 ;
  returns : coordinate x4 y4 ;

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x5 ;

  inputs : x5 ;
  operation : decisionMC particles epsilon "p5" (const [1 .. 10]) ;
  outputs : y5 ;
  returns : coordinate x5 y5 ;

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x6 ;

  inputs : x6 ;
  operation : decisionMC particles epsilon "p6" (const [1 .. 10]) ;
  outputs : y6 ;
  returns : coordinate x6 y6 ;

  operation : nature (uniformD [1 .. 10]) ;
  outputs : x7 ;

  inputs : x7 ;
  operation : decisionMC particles epsilon "p7" (const [1 .. 10]) ;
  outputs : y7 ;
  returns : coordinate x7 y7 ;

  :-----:
  outputs: ;
|]
