{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}



module Examples.Governance.InstitutionProcess
  where

import OpenGames.Engine.Engine
import OpenGames.Preprocessor

--------------------------
-- 0. Payoffs
-- 0.0 Share-cropping

productionFunction :: Double -> Double -> Double
productionFunction tech effort = tech*effort

payoffWorkerShare,payoffLandLordShare :: Double -> Double -> Double
payoffWorkerShare amount share = amount*share
payoffLandLordShare amount share = amount *(1-share)

-- 0.1 wage setting game
payoffLandLordWage :: Double -> Double -> Double
payoffLandLordWage amount wage = amount - wage

payoffWorkerWage :: Double -> Double
payoffWorkerWage wage  = wage


-- 0.2 voting function
majority :: Double -> Either () () -> Either () () -> Either Double Double
majority tech (Left ()) (Left ()) = Left tech
majority tech (Right ()) (Right ()) = Right tech
majority tech _ _ = Left tech

-- 0.3 random choice of institutional
regimeChoice :: Double -> [Char] -> Either Double Double
regimeChoice tech "cr" = Left tech
randomTegime tech "wa" = Right tech

--------------------------
-- 1. Preliminary Stage
-- Nature determining the technology 

technologySrc = Block [] []
                     [Line Nothing [] [] "nature (uniform [0, 0.1 .. 1])" ["tech"] []]
                     ["tech"] []


--------------------------
-- 2. Administrative Stage
-- 2.0 Landowners setting the share 


technology = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ; 
   feedback  : ;
   operation : natureDraw dist;
   outputs   : tech ;
   returns   : ;
   :----------------------------:

   outputs   : tech ;
   returns   : ; 
  |]
  where
   dist = uniformDist [0, 0.1 .. 1]

 --------------------------
-- 2. Administrative Stage
-- 2.0 Landowners setting the share 

landLordShare = [opengame|
   inputs    : tech  ;
   feedback  :   ;

   :----------------------------:
   inputs    : tech; 
   feedback  : ;
   operation : dependentDecision "landLord" actionSpace ;
   outputs   : share ;
   returns   : payoffLandLordShare (productionFunction tech effort) share ;
   :----------------------------:

   outputs   : share ;
   returns   : effort ; 
  |]
  where
    actionSpace = (const [0, 0.1 .. 1])


-- 2.1 Landowners setting the wage

landLordWage = [opengame|
   inputs    : tech  ;
   feedback  :   ;

   :----------------------------:
   inputs    : tech; 
   feedback  : ;
   operation : dependentDecision "landLord" actionSpace ;
   outputs   : wage ;
   returns   : payoffLandLordWage (productionFunction tech effort) wage ;
   :----------------------------:

   outputs   : wage ;
   returns   : effort ; 
  |]
  where
    actionSpace = (const [0, 1 .. 10])


--------------------------
-- 3. Substantive Stage
-- 3.0 Workers spending effort

workerShare = [opengame|
   inputs    : tech, share  ;
   feedback  :   ;

   :----------------------------:
   inputs    : tech; 
   feedback  : ;
   operation : dependentDecision "worker" actionSpace ;
   outputs   : effort ;
   returns   : payoffWorkerShare (productionFunction tech effort) share ;
   :----------------------------:

   outputs   : effort ;
   returns   :  ; 
  |]
  where
    actionSpace = (const [0, 1 .. 10])



-- 3.1 Substantive Stage
-- Workers spending effort

workerWage = [opengame|
   inputs    : wage  ;
   feedback  :   ;

   :----------------------------:
   inputs    : wage ; 
   feedback  : ;
   operation : dependentDecision "worker" actionSpace ;
   outputs   : effort ;
   returns   : payoffWorkerWage wage ;
   :----------------------------:

   outputs   : effort ;
   returns   :  ; 
  |]
  where
    actionSpace = (const [0, 1 .. 10])


--------------------------
-- 4. Partial continuation games for each institutional arrangement
-- 4.0 share-cropping

cropGame = [opengame|
   inputs    : tech  ;
   feedback  : effort  ;

   :----------------------------:
   inputs    : tech ; 
   feedback  : ;
   operation : landLordShare ;
   outputs   : share ;
   returns   : effort ;

   inputs    : tech, share ; 
   feedback  : ;
   operation : workerShare ;
   outputs   : effort ;
   returns   :  ;
   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]

-- 4.1 wage setting

wageGame = [opengame|
   inputs    : tech  ;
   feedback  : effort  ;

   :----------------------------:
   inputs    : tech ; 
   feedback  : ;
   operation : landLordWage ;
   outputs   : wage ;
   returns   : effort ;

   inputs    : wage ; 
   feedback  : ;
   operation : workerWage ;
   outputs   : effort ;
   returns   :  ;
   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]

--------------------------
-- 5  Voting game

votingInst = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ; 
   feedback  : ;
   operation : dependentDecision "gov1" actionSpace ;
   outputs   : vote1 ;
   returns   : 0 ;

   inputs    : ; 
   feedback  : ;
   operation : dependentDecision "gov2" actionSpace ;
   outputs   : vote2 ;
   returns   : 0 ;

   :----------------------------:

   outputs   :  vote1, vote2 ;
   returns   :  ; 
  |]
  where
    actionSpace = (const [Left (), Right ()])

--------------------------
-- 6. Putting the whole game together
-- 6.0 Simple share-cropping

cropGameComplete = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ;
   feedback  : ;
   operation : technology ;
   outputs   : tech ;
   returns   :  ;

   inputs    : tech ;
   feedback  : ;
   operation : landLordShare ;
   outputs   : share ;
   returns   : effort ;

   inputs    : tech, share ;
   feedback  : ;
   operation : workerShare ;
   outputs   : effort ;
   returns   :  ;


   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]


  -- 6.1 Simple wage-setting

wageGameComplete = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ;
   feedback  : ;
   operation : technology ;
   outputs   : tech ;
   returns   :  ;

   inputs    : tech ;
   feedback  : ;
   operation : landLordWage ;
   outputs   : wage ;
   returns   : effort ;

   inputs    : wage ;
   feedback  : ;
   operation : workerWage ;
   outputs   : effort ;
   returns   :  ;


   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]

-- 6.2 Branching game with actual choice
branchingGame = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ;
   feedback  : ;
   operation : technology ;
   outputs   : tech ;
   returns   :  ;

   inputs    : ;
   feedback  : ;
   operation : votingInst ;
   outputs   : vote1,vote2 ;
   returns   :  ;

   inputs    : majority tech vote1 vote2 ;
   feedback  : discard1 ;
   operation : branchGame cropGame wageGame ;
   outputs   : discard2 ;
   returns   :  ;


   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]
  where branchGame = (+++)

-- 6.3 Random evolution of institution
randomInst = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ;
   feedback  : ;
   operation : technology ;
   outputs   : tech ;
   returns   :  ;

   inputs    : ;
   feedback  : ;
   operation : nature distribution ;
   outputs   : inst ;
   returns   :  ;

   inputs    : regimeChoice tech inst ;
   feedback  : discard1 ;
   operation : branchGame cropGame wageGame ;
   outputs   : discard2 ;
   returns   :  ;


   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]
  where
    distribution = uniformDist actionSpace
    actionSpace = ["cr","wa"]
    branchGame = (+++)



-- 6.4 Dictator deciding the institution; payoff based on the effort spent
dictatorInstSrc = Block [] []
                 [Line Nothing [] [] "technology" ["tech"] [],
                  Line Nothing [] [] "dependentDecision \"dictator\" (const [\"cr\", \"wa\"])" ["inst"] ["effort"],
                  Line Nothing ["regimeChoice tech inst"] ["effort"] "cropGame +++ wageGame " ["discard"] []
                 ]
                 [] []
dictatorInst = [opengame|
   inputs    :   ;
   feedback  :   ;

   :----------------------------:
   inputs    : ;
   feedback  : ;
   operation : technology ;
   outputs   : tech ;
   returns   :  ;

   inputs    : ;
   feedback  : ;
   operation : dependentDecision "dictator" (const actionSpace) ;
   outputs   : inst ;
   returns   : effort ;

   inputs    : regimeChoice tech inst ;
   feedback  : effort ;
   operation : branchGame cropGame wageGame ;
   outputs   : discard2 ;
   returns   :  ;


   :----------------------------:

   outputs   :  ;
   returns   :  ; 
  |]
  where
    actionSpace = ["cr","wa"]
    branchGame = (+++)

-- 6 eq checks
eqCropGame strat = generateIsEq $ evaluate cropGameComplete strat void
eqWageGame strat = generateIsEq $ evaluate wageGameComplete strat void
eqBranchGame strat = generateIsEq $ evaluate branchingGame strat void
eqRandomInstGame strat = generateIsEq $ evaluate randomInst strat void
eqDictatorInstGame strat = generateIsEq $ evaluate dictatorInst strat void

-- 7 strategies

-- crop game
landLordShareStrat x = pureAction x
workerShareStrat x = pureAction x

cropGameStratTuple x y =
  landLordShareStrat x
  ::- workerShareStrat y
  ::- Nil

-- wage game
landLordWageStrat x = pureAction x
workerWageStrat x = pureAction x

wageGameStratTuple x y =
  landLordWageStrat x
  ::- workerWageStrat y
  ::- Nil

-- branching game
votingStrategy x = pureAction x

branchingGameStrategy vote1 vote2 share1 share2 wage1 wage2 =
  votingStrategy vote1
  ::- votingStrategy vote2
  ::- landLordShareStrat share1
  ::- workerShareStrat share2
  ::- landLordWageStrat wage1
  ::- workerWageStrat wage2
  ::- Nil

 

-- Usage
-- eqCropGame $ cropGameStratTuple 0.5 0.5
-- eqCropGame $ cropGameStratTuple 0 10
-- eqWageGame $ wageGameStratTuple 0 10
-- branchingGameStrategy (Left ()) (Left ()) 1 1 1 1
-- eqBranchGame $ branchingGameStrategy (Left ()) (Left ()) 0 10 0 10
