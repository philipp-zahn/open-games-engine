{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Examples.BranchingMoves where


import Engine.Engine
import Preprocessor.Preprocessor


import Examples.SimultaneousMoves (prisonersDilemmaVerbose,meetingInNYReduced, ActionPD,Location)


-- available games
data Games = PD | MNY
  deriving (Eq,Show,Ord)



{-
-- Player 1 chooses the game for players 2 and 3
chooseDilemma :: OpenGame
                           StochasticStatefulOptic
                           StochasticStatefulContext
                           ('[Kleisli Stochastic () Games,
                              Kleisli Stochastic () Examples.SimultaneousMoves.ActionPD,
                              Kleisli Stochastic () Examples.SimultaneousMoves.ActionPD,
                              Kleisli Stochastic () Examples.SimultaneousMoves.Location,
                              Kleisli Stochastic () Examples.SimultaneousMoves.Location])
                           ('[[DiagnosticInfoBayesian () Games]
                             , Maybe [DiagnosticInfoBayesian () ActionPD]
                              ])
                           ()
                           ()
                           ()
                           () 
chooseDilemma = [opengame|

   inputs    :      ;
   feedback  :      ;

   :----------------------------:
   inputs    :      ;
   feedback  :      ;
   operation : dependentDecision "player3" (const [PD,MNY]);
   outputs   : decisionPlayer3 ;
   returns   : 0 ;
   // player 3 gets no payoff 

   operation : branchingOperation prisonersDilemmaVerbose  meetingInNYReduced ;

   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]
branchingPDMeetingINNY :: OpenGame
                            StochasticStatefulOptic
                            StochasticStatefulContext
                            '[Kleisli Stochastic () ActionPD
                             , Kleisli Stochastic () ActionPD
                             , Kleisli Stochastic () Integer]
                            '[Maybe [DiagnosticInfoBayesian () ActionPD]
                             , Maybe [DiagnosticInfoBayesian () ActionPD]
                             , Maybe [DiagnosticInfoBayesian () Integer]]
                            (Either () ())
                            ()
                            (Either () ())
                            ()
branchingPDMeetingINNY =  prisonersDilemmaVerbose +++  player1Move --  meetingInNYReduced



--}
branchingPDMeetingINNY :: OpenGame
                            StochasticStatefulOptic
                            StochasticStatefulContext
                            '[Kleisli Stochastic () ActionPD
                             , Kleisli Stochastic () ActionPD
                             , Kleisli Stochastic () Integer]
                            '[Maybe [DiagnosticInfoBayesian () ActionPD]
                             , Maybe [DiagnosticInfoBayesian () ActionPD]
                             , Maybe [DiagnosticInfoBayesian () Integer]]
                            (Either () ())
                            ()
                            (Either () ())
                            ()
branchingPDMeetingINNY = player1Move +++  prisonersDilemmaVerbose --  meetingInNYReduced

test = (+++) prisonersDilemmaVerbose 

player1Move =  [opengame|

   inputs    :      ;
   feedback  :      ;

   :----------------------------:
   inputs    :      ;
   feedback  :      ;
   operation : dependentDecision "player1" (const [1,2]);
   outputs   : decisionPlayer1 ;
   returns   : 0 ;
   // player 1 gets no payoff 

   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]


player2Move =  [opengame|

   inputs    :      ;
   feedback  :      ;

   :----------------------------:
   inputs    :      ;
   feedback  :      ;
   operation : dependentDecision "player2" (const [1,2]);
   outputs   : decisionPlayer2 ;
   returns   : 0 ;
   // player 2 gets no payoff 

   :----------------------------:

   outputs   :      ;
   returns   :      ;
  |]

branchedGame = player1Move +++ player2Move
