{-# LANGUAGE DataKinds, NamedFieldPuns, DisambiguateRecordFields, LambdaCase, RecordWildCards, OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NamedFieldPuns #-}

module Engine.IOGames
  ( IOOpenGame(..)
  , Agent(..)
  , DiagnosticsMC(..)
  , dependentDecisionIO
  , fromLens
  , fromFunctions
  , nature
  , discount
  , Msg(..)
  , PlayerMsg(..)
  , SamplePayoffsMsg(..)
  , AverageUtilityMsg(..)
  , DiagnosticsMC
  , logFuncSilent
  , logFuncTracing
  , logFuncStructured
  ) where


import System.Directory
import           GHC.Stack
import           Control.Monad.Reader
import           Data.Bifunctor
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as S8
import           Data.Functor.Contravariant
import           Data.IORef
import           Debug.Trace
import qualified RIO
import           RIO (RIO, glog, GLogFunc, HasGLogFunc(..))

import           Control.Arrow hiding ((+:+))
import           Control.Monad.Bayes.Weighted
import           Control.Monad.State hiding (state)
import           Control.Monad.Trans.Class
import           Data.Foldable
import           Data.HashMap as HM hiding (null,map,mapMaybe)
import           Data.List (maximumBy)
import           Data.Ord (comparing)
import           Data.Utils
import qualified Data.Vector as V
import           GHC.TypeLits
import           Numeric.Probability.Distribution hiding (map, lift)
import           System.Random.MWC.CondensedTable
import           System.Random
import           System.Random.Stateful

import           Engine.OpenGames hiding (lift)
import           Engine.OpticClass
import           Engine.TLL
import           Engine.Diagnostics

--------------------------------------------------------------------------------
-- Messaging

-- TODO implement printout

type IOOpenGame a b x s y r = OpenGame MonadOptic MonadContext a b x s y r

type Agent = String


data DiagnosticsMC y = DiagnosticsMC {
  playerNameMC :: String
  , averageUtilStrategyMC :: Double
  , samplePayoffsMC :: [Double]
  , optimalMoveMC :: y
  , optimalPayoffMC :: Double
  }
  deriving (Show)

-- NOTE This ignores the state
dependentDecisionIO :: (Eq x, Show x, Ord y, Show y) => String -> Int -> [y] ->  IOOpenGame '[Kleisli CondensedTableV x y] '[IO (DiagnosticsMC y)] x () y Double
          -- s t  a b
-- ^ (average utility of current strategy, [average utility of all possible alternative actions])
dependentDecisionIO name sampleSize ys = OpenGame { play, evaluate} where
  -- ^ ys is the list of possible actions
  play = \(strat ::- Nil) -> let v x = do
                                   g <- newStdGen
                                   gS <- newIOGenM g
                                   action <- genFromTable (runKleisli strat x) gS
                                   return ((),action)
                                 u () r = modify (adjustOrAdd (+ r) r name)
                             in MonadOptic v u

  evaluate (strat ::- Nil) (MonadContext h k) =
    output ::- Nil

    where

      output = do
        zippedLs <- samplePayoffs
        let samplePayoffs' = map snd zippedLs
        let (optimalPlay, optimalPayoff0) = maximumBy (comparing snd) zippedLs
        (currentMove, averageUtilStrategy') <- averageUtilStrategy
        return  DiagnosticsMC{
            playerNameMC = name
          , averageUtilStrategyMC = averageUtilStrategy'
          , samplePayoffsMC = samplePayoffs'
          , optimalMoveMC = optimalPlay
          , optimalPayoffMC = optimalPayoff0
          }

        where
           action = do
              (_,x) <- h
              g <- newStdGen
              gS <- newIOGenM g
              genFromTable (runKleisli strat x) gS
           u y     = do
              (z,_) <- h
              evalStateT (do
                             r <- k z y
                           -- ^ utility <- payoff function given other players strategies and my own action y
                             gets ((+ r) . HM.findWithDefault 0.0 name))
                          HM.empty
           -- Sample the average utility from current strategy
           averageUtilStrategy = do
             (_,x) <- h
             actionLS' <- replicateM sampleSize action
             utilLS  <- mapM u actionLS'
             let average = (sum utilLS / fromIntegral sampleSize)
             return (x,average)
           -- Sample the average utility from a single action
           sampleY y = do
                  ls1 <- replicateM sampleSize (u y)
                  let average =  (sum ls1 / fromIntegral sampleSize)
                  pure (y, average)
           -- Sample the average utility from all actions
           samplePayoffs  = mapM sampleY ys



-- Support functionality for constructing open games
fromLens :: (x -> y) -> (x -> r -> s) -> IOOpenGame msg '[] '[] x s y r
fromLens v u = OpenGame {
  play = \Nil -> MonadOptic (\x -> return (x, v x)) (\x r -> return (u x r)),
  evaluate = \Nil _ -> Nil}


fromFunctions :: (x -> y) -> (r -> s) -> IOOpenGame msg '[] '[] x s y r
fromFunctions f g = fromLens f (const g)

nature :: CondensedTableV x -> IOOpenGame  '[] '[] () () x ()
nature table = OpenGame { play, evaluate} where
  play _ =
    MonadOptic v u
    where
      v () = do
        g <- newStdGen
        gS <- newIOGenM g
        draw <- genFromTable table gS
        return ((),draw)
      u _ _ = return ()

  evaluate = \_ _ -> Nil



-- discount Operation for repeated structures
discount :: String -> (Double -> Double) -> IOOpenGame msg '[] '[] () () () ()
discount name f = OpenGame {
  play = \_ -> let v () = return ((), ())
                   u () () = modify (adjustOrAdd f (f 0) name)
                 in MonadOptic v u,
  evaluate = \_ _ -> Nil}

--------------------------------------------------------------------------------
-- Logging

logFuncSilent :: CallStack -> Msg action -> IO ()
logFuncSilent _ _ = pure ()

-- ignore this one
logFuncTracing :: Show action => CallStack -> Msg action -> IO ()
logFuncTracing _ (AsPlayer _ (SamplePayoffs (SampleRootMsg _ (CalledK {})))) = pure ()
logFuncTracing _ (AsPlayer _ (AverageUtility (AverageRootMsg (CalledK {})))) = pure ()
logFuncTracing callStack msg = do
  case getCallStack callStack of
     [("glog", srcloc)] -> do
       -- This is slow - consider moving it elsewhere if speed becomes a problem.
       fp <- makeRelativeToCurrentDirectory (srcLocFile srcloc)
       S8.putStrLn (S8.pack (prettySrcLoc0 (srcloc{srcLocFile=fp}) ++ show msg))
     _ -> error "Huh?"

prettySrcLoc0 :: SrcLoc -> String
prettySrcLoc0 SrcLoc {..}
  = foldr (++) ""
      [ srcLocFile, ":"
      , show srcLocStartLine, ":"
      , show srcLocStartCol, ": "
      ]

data Readr = Readr { indentRef :: IORef Int }
logFuncStructured indentRef _ msg = flip runReaderT Readr{indentRef} (go msg)

  where

   go = \case
     AsPlayer player msg -> do
       case msg of
         Outputting -> pure ()
         SamplePayoffs pmsg ->
           case pmsg of
             SampleAction action -> logln ("SampleY: " ++ take 1 (show action))
             SampleRootMsg i msg -> do
               case msg of
                 UStart -> logstr "u["
                 CalledK msg -> case msg of
                   VChooseAction action -> logstr (take 1 (show action))
                   _ -> pure ()
                 UEnd -> do logstr "]"; newline
                 _ -> pure ()
             _ -> pure ()
         _ -> pure ()
     _ -> pure ()

   logln :: String -> (ReaderT Readr IO) ()
   logln s = do newline; logstr s; newline

   logstr :: String -> (ReaderT Readr IO) ()
   logstr s = liftIO $ S8.putStr (S8.pack s)

   newline  :: ReaderT Readr IO ()
   newline =
      do Readr{indentRef} <- ask
         liftIO $
          do i <- readIORef indentRef
             S8.putStr ("\n" <> S8.replicate i ' ')


   indent :: ReaderT Readr IO ()
   indent = (do Readr{indentRef} <- ask; liftIO $ modifyIORef' indentRef (+4))

   deindent :: ReaderT Readr IO ()
   deindent =  (do Readr{indentRef} <- ask; liftIO $ modifyIORef' indentRef (subtract 4))
