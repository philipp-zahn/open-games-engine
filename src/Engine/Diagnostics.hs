{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Engine.Diagnostics
  ( DiagnosticInfoBayesian(..)
  , generateOutput
  , generateIsEq
  , generateEquilibrium
  ) where

import Engine.OpticClass
import Engine.TLL


--------------------------------------------------------
-- Diagnosticinformation and processesing of information
-- for standard game-theoretic analysis

-- Defining the necessary types for outputting information of a BayesianGame
data DiagnosticInfoBayesian x y = DiagnosticInfoBayesian
  { equilibrium     :: Bool
  , player          :: String
  , optimalMove     :: y
  , strategy        :: Stochastic y
  , optimalPayoff   :: Double
  , context         :: (y -> Double)
  , payoff          :: Double
  , state           :: x
  , unobservedState :: String}


-- prepare string information for Bayesian game
showDiagnosticInfo :: (Show y, Ord y, Show x) => DiagnosticInfoBayesian x y -> String
showDiagnosticInfo info =  
     "\n"    ++ "Player: " ++ player info
     ++ "\n" ++ "Optimal Move: " ++ (show $ optimalMove info)
     ++ "\n" ++ "Current Strategy: " ++ (show $ strategy info)
     ++ "\n" ++ "Optimal Payoff: " ++ (show $ optimalPayoff info)
     ++ "\n" ++ "Current Payoff: " ++ (show $ payoff info)
     ++ "\n" ++ "Observable State: " ++ (show $ state info)
     ++ "\n" ++ "Unobservable State: " ++ (show $ unobservedState info)



-- output string information for a subgame expressions containing information from several players - bayesian 
showDiagnosticInfoL :: (Show y, Ord y, Show x) => [DiagnosticInfoBayesian x y] -> String
showDiagnosticInfoL [] = "\n --No more information--"
showDiagnosticInfoL (x:xs)  = showDiagnosticInfo x ++ "\n --other game-- " ++ showDiagnosticInfoL xs 

-- checks equilibrium and if not outputs relevant deviations
checkEqL :: (Show y, Ord y, Show x) => [DiagnosticInfoBayesian x y] -> String
checkEqL ls = let xs = fmap equilibrium ls
                  ys = filter (\x -> equilibrium x == False) ls
                  isEq = and xs
                  in if isEq == True then "\n Strategies are in equilibrium"
                                      else "\n Strategies are NOT in equilibrium. Consider the following profitable deviations: \n"  ++ showDiagnosticInfoL ys

-- map diagnostics to equilibrium
toEquilibrium :: DiagnosticInfoBayesian x y -> Bool
toEquilibrium = equilibrium

equilibriumMap :: [DiagnosticInfoBayesian x y] -> Bool
equilibriumMap = and . fmap toEquilibrium


----------------------------------------------------------
-- providing the relevant functionality at the type level
-- for show output

data ShowDiagnosticOutput = ShowDiagnosticOutput

instance (Show y, Ord y, Show x) => Apply ShowDiagnosticOutput [DiagnosticInfoBayesian x y] String where
  apply _ x = showDiagnosticInfoL x


data PrintIsEq = PrintIsEq

instance (Show y, Ord y, Show x) => Apply PrintIsEq [DiagnosticInfoBayesian x y] String where
  apply _ x = checkEqL x


data PrintOutput = PrintOutput

instance (Show y, Ord y, Show x) => Apply PrintOutput [DiagnosticInfoBayesian x y] String where
  apply _ x = showDiagnosticInfoL x


data Concat = Concat

instance Apply Concat String (String -> String) where
  apply _ x = \y -> x ++ "\n NEWGAME: \n" ++ y

-- for apply output of equilibrium function
data Equilibrium = Equilibrium 

instance Apply Equilibrium [DiagnosticInfoBayesian x y] Bool where
  apply _ x = equilibriumMap x

data And = And

instance Apply And Bool (Bool -> Bool) where
  apply _ x = \y -> y && x


---------------------
-- main functionality

-- all information for all players
generateOutput :: forall xs.
               ( MapL   PrintOutput xs     (ConstMap String xs)
               , FoldrL Concat String (ConstMap String xs)
               ) => List xs -> IO ()
generateOutput hlist = putStrLn $
  "----Analytics begin----" ++ (foldrL Concat "" $ mapL @_ @_ @(ConstMap String xs) PrintOutput hlist) ++ "----Analytics end----\n"

-- output equilibrium relevant information
generateIsEq :: forall xs.
               ( MapL   PrintIsEq xs     (ConstMap String xs)
               , FoldrL Concat String (ConstMap String xs)
               ) => List xs -> IO ()
generateIsEq hlist = putStrLn $
  "----Analytics begin----" ++ (foldrL Concat "" $ mapL @_ @_ @(ConstMap String xs) PrintIsEq hlist) ++ "----Analytics end----\n"

-- give equilibrium value for further use
generateEquilibrium :: forall xs.
              ( MapL   Equilibrium xs     (ConstMap Bool xs)
               , FoldrL And Bool (ConstMap Bool xs)
               ) => List xs -> Bool
generateEquilibrium hlist = foldrL And True $ mapL @_ @_ @(ConstMap Bool xs) Equilibrium hlist
