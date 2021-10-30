module Engine.Diagnostics

import Data.List

import Engine.OpticClass

--------------------------------------------------------
-- Diagnosticinformation and processesing of information
-- for standard game-theoretic analysis

-- Defining the necessary types for outputting information of a BayesianGame
public export
record DiagnosticInfoBayesian (x, y : Type) where
  constructor MkDiagnosticInfoBayesian
  equilibrium     : Bool
  player          : String
  optimalMove     : y
  strategy        : Stochastic y
  optimalPayoff   : Double
  context         : (y -> Double)
  payoff          : Double
  state           : x
  unobservedState : String


-- prepare string information for Bayesian game
export
showDiagnosticInfo : (Show y, Ord y, Show x) => DiagnosticInfoBayesian x y -> String
showDiagnosticInfo info =  """
     Player: \{player info}
     Optimal Move: \{show $ optimalMove info}
     Current Strategy: \{show $ strategy info}
     Optimal Payoff: \{show $ optimalPayoff info}
     Current Payoff: \{show $ payoff info}
     Observable State: \{show $ state info}
     Unobservable State: \{show $ unobservedState info}
     """

-- output string information for a subgame expressions containing information from several players - bayesian 
export
showDiagnosticInfoL : (Show y, Ord y, Show x) => List (DiagnosticInfoBayesian x y) -> String
showDiagnosticInfoL [] = "\n --No more information--"
showDiagnosticInfoL (x :: xs)  = showDiagnosticInfo x ++ "\n --other game-- " ++ showDiagnosticInfoL xs 

-- checks equilibrium and if not outputs relevant deviations
export
checkEqL : (Show y, Ord y, Show x) => List (DiagnosticInfoBayesian x y) -> String
checkEqL ls = let (eq, notEq)  = partition equilibrium ls 
               in if null notEq then "\n Strategies are in equilibrium"
                                else "\n Strategies are NOT in equilibrium. Consider the following profitable deviations: \n"  ++ showDiagnosticInfoL notEq

----------------------------------------------------------
-- providing the relevant functionality at the type level
-- for show output

-- data ShowDiagnosticOutput = ShowDiagnosticOutput
-- 
-- instance (Show y, Ord y, Show x) => Apply ShowDiagnosticOutput [DiagnosticInfoBayesian x y] String where
--   apply _ x = showDiagnosticInfoL x
-- 
-- 
-- data PrintIsEq = PrintIsEq
-- 
-- instance (Show y, Ord y, Show x) => Apply PrintIsEq [DiagnosticInfoBayesian x y] String where
--   apply _ x = checkEqL x
-- 
-- 
-- data PrintOutput = PrintOutput
-- 
-- instance (Show y, Ord y, Show x) => Apply PrintOutput [DiagnosticInfoBayesian x y] String where
--   apply _ x = showDiagnosticInfoL x
-- 
-- 
-- data Concat = Concat
-- 
-- instance Apply Concat String (String -> String) where
--   apply _ x = \y => x ++ "\n NEWGAME: \n" ++ y


---------------------
-- main functionality

-- all information for all players
-- generateOutput : forall xs.
--                ( MapL   PrintOutput xs     (ConstMap String xs)
--                , FoldrL Concat String (ConstMap String xs)
--                ) => List xs -> IO ()
-- generateOutput hlist = 
--   putStrLn $
--   "----Analytics begin----" ++ (foldrL Concat "" $ mapL @_ @_ @(ConstMap String xs) PrintOutput hlist) ++ "----Analytics end----\n"

-- output equilibrium relevant information
-- generateIsEq : forall xs.
--                ( MapL   PrintIsEq xs     (ConstMap String xs)
--                , FoldrL Concat String (ConstMap String xs)
--                ) => List xs -> IO ()
-- generateIsEq hlist = putStrLn $
--   "----Analytics begin----" ++ (foldrL Concat "" $ mapL @_ @_ @(ConstMap String xs) PrintIsEq hlist) ++ "----Analytics end----\n"
-- 
{-
-}
