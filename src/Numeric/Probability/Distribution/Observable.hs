{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls, ImplicitParams #-}

-- | Observable distribution monad.

module Numeric.Probability.Distribution.Observable
  ( T
  , decons
  , fromFreqs
  , certainly
  , expected
  , mapMaybe
  , uniform
  , observeT
  , toT
  , note
  ) where

import           Control.Monad
import           Control.Monad.Reader
import           Data.ByteString (ByteString)
import qualified Data.ByteString as S
import qualified Data.ByteString.Char8 as S8
import           Data.IORef
import qualified Data.List as List
import           Data.String
import           GHC.Stack
import qualified Numeric.Probability.Distribution as I
import           System.IO.Unsafe

data T p a where
  FromFreqs :: Fractional p => CallStack -> [(a,p)] -> T p a
  Certainly :: CallStack -> a -> T p a
  MapMaybe :: Fractional prob => CallStack -> (a -> Maybe b) -> T prob a -> T prob b
  Uniform :: Fractional prob => CallStack -> [a] -> T prob a
  Bind :: T p x -> (x -> T p b) -> T p b
  Note :: CallStack -> String -> T p ()

instance (Num prob, Ord prob, Show prob, Ord a, Show a) => Show (T prob a) where
  show _ = "T"

instance (Num prob) => Monad (T prob) where
  return = pure
  (>>=) = Bind

instance Num prob => Applicative (T prob) where
  pure = Certainly emptyCallStack
  (<*>) = ap

instance Num prob => Functor (T prob) where
  fmap = liftM

--------------------------------------------------------------------------------
-- Interpetable

fromFreqs :: (Fractional p, HasCallStack) => [(a,p)] -> T p a
fromFreqs = FromFreqs callStack

certainly :: HasCallStack => a -> T p a
certainly = Certainly callStack

mapMaybe ::
     (Fractional prob, HasCallStack) => (a -> Maybe b) -> T prob a -> T prob b
mapMaybe = MapMaybe callStack

uniform :: (Fractional prob, HasCallStack) => [a] -> T prob a
uniform = Uniform callStack

note :: HasCallStack => String -> T prob ()
note = Note callStack

--------------------------------------------------------------------------------
-- Exports; this is where the monad is "run" and where we can
-- reasonably print a trace.

{-# NOINLINE decons #-}
decons :: (Num p, Fractional p) => T p a -> [(a,p)]
decons t = unsafePerformIO (observeT t)

expected :: (Num a, Fractional a) => T a a -> a
expected = sum . List.map (\(x,p) -> x * p) . decons

--------------------------------------------------------------------------------
-- Reflection

toT :: Num p => T p a -> I.T p a
toT =
  \case
    Uniform _ as -> I.uniform as
    FromFreqs _ fs -> I.fromFreqs fs
    Certainly _ a -> I.certainly a
    MapMaybe _ f x -> I.mapMaybe f (toT x)
    Bind m f -> toT m >>= toT . f
    Note _ _ -> pure ()

--------------------------------------------------------------------------------
-- Reflection with printing

data Stats = Stats
  { uniformCalls :: !Int
  , bindCalls :: !Int
  , noteCalls :: !Int
  } deriving (Show)

observeT :: (Num p, Fractional p) => T p a -> IO [(a,p)]
observeT m = do
  S8.putStr "Observing ..."
  stats <- newIORef (Stats 0 0 0)
  dots <- newIORef 0
  let go :: (Num p, Fractional p) => T p a -> ReaderT Int IO [(a, p)]
      go =
        \case
          Bind m f -> do
            liftIO
              (modifyIORef'
                 stats
                 (\Stats {..} -> Stats {bindCalls = bindCalls + 1, ..}))
            xps <- local (+ 2) (go m)
            if null xps
              then do
                pure []
              else do
                yqps <-
                  local
                    (+ 2)
                    (traverse
                       (\(_i, (x, p))

                         -> do
                          yqs <- local (+ 2) (go (f x))
                          pure (map (\(y, q) -> (y, q * p)) yqs))
                       (zip [1 :: Int ..] xps))
                pure (concat yqps)
          Uniform _c as -> do
            liftIO
              (modifyIORef'
                 stats
                 (\Stats {..} -> Stats {uniformCalls = uniformCalls + 1, ..}))
            pure (I.decons (I.uniform as))
          FromFreqs _c as -> do
            pure (I.decons (I.fromFreqs as))
          Certainly _c as -> do
            pure (I.decons (I.certainly as))
          MapMaybe _c f as -> do
            as' <- go as
            pure (I.decons (I.mapMaybe f (I.fromFreqs as')))
          Note _c no -> do
            liftIO
              (modifyIORef'
                 stats
                 (\Stats {..} -> Stats {noteCalls = noteCalls + 1, ..}))
            pure [((), 1)]
      _smallCs c =
        case getCallStack c of
          [] -> "(no call stack)"
          ((_, srcloc):_) -> prettySrcLoc srcloc
  x <- flip runReaderT 0 (go m)
  S8.putStrLn "done:"
  stats' <- readIORef stats
  print stats'
  pure x
