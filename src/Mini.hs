{-# language DataKinds, TypeOperators, GADTs, MultiParamTypeClasses, KindSignatures, FlexibleInstances, FlexibleContexts, TypeFamilies, FunctionalDependencies, UndecidableInstances, QuasiQuotes, NamedFieldPuns, PartialTypeSignatures, ScopedTypeVariables, GeneralizedNewtypeDeriving , OverloadedStrings, Rank2Types, ConstraintKinds, LambdaCase, RecordWildCards #-}

-- |



import           Control.Applicative ( Applicative(liftA2) )
import           Control.Arrow ( Kleisli(runKleisli, Kleisli) )
import           Control.Monad.Reader
import           Control.Monad.State ( StateT(StateT), replicateM_ )
import           Control.Monad.State ( StateT, replicateM, gets, modify, evalStateT )
import qualified Control.Monad.State as ST
    ( MonadState(put, get), MonadTrans(lift), StateT(runStateT) )
import           Control.Monad.Trans.Class as Trans ( MonadTrans(lift) )
import qualified Data.ByteString.Char8 as S8
import           Data.Foldable
import           Data.Functor.Contravariant
import qualified Data.HashMap as HM ( empty, findWithDefault, Map, lookup )
import           Data.IORef
import           Data.Kind ( Type, Constraint )
import           Data.List (maximumBy)
import           Data.Ord
import           Data.Proxy
import           Data.Utils ( adjustOrAdd )
import           Data.Utils ( average )
import qualified Data.Vector as V ( fromList )
import           Debug.Trace ()
import           GHC.Stack
import           Numeric.Probability.Distribution ( certainly )
import           Numeric.Probability.Distribution ( fromFreqs, T(decons) )
import           Preprocessor.Preprocessor ( opengame )
import qualified RIO
import           RIO (RIO, runRIO, GLogFunc, glog, mkGLogFunc, mapRIO)
import           System.Directory
import           System.IO.Unsafe ( unsafePerformIO )
import           System.Random ( newStdGen )
import           System.Random.MWC.CondensedTable
    ( CondensedTableV, tableFromProbabilities )
import           System.Random.MWC.CondensedTable ( genFromTable, CondensedTableV )
import           System.Random.Stateful ( newIOGenM )
import           Text.Printf

main = printOutput 20 (transformStratTuple strategyTupleTest) (Cooperate,Cooperate)

--------------------------------------------------------------------------------
-- Mini-RIO

type Rdr = GLogFunc Msg

data Msg = AsPlayer String PlayerMsg | UStart | UEnd | WithinU Msg | CalledK Msg | VChooseAction ActionPD
  deriving Show
data PlayerMsg = Outputting | SamplePayoffs SamplePayoffsMsg | AverageUtility AverageUtilityMsg
  deriving Show
data SamplePayoffsMsg = SampleAction ActionPD | SampleRootMsg Int Msg | SampleAverageIs Double
  deriving Show
data AverageUtilityMsg = StartingAverageUtil | AverageRootMsg Msg | AverageActionChosen ActionPD | AverageIterAction Int ActionPD | AverageComplete Double
  deriving Show
--------------------------------------------------------------------------------
-- TLL

infixr 6 ::-
data List ts where
  Nil :: List '[]
  (::-) :: t -> List ts -> List (t ': ts)

instance Show (List '[]) where
    show Nil = "Nil"

instance (Show (List as), Show a)
    => Show (List (a ': as)) where
    show (a ::- rest) =
        show a ++ " ::- " ++ show rest


type family (+:+) (as :: [*]) (bs :: [*]) :: [*] where
  '[] +:+ bs = bs
  (a ': as) +:+ bs = a ': (as +:+ bs)

(+:+) :: List as -> List bs -> List (as +:+ bs)
(+:+) Nil bs = bs
(+:+) (a ::- as) bs = a ::- as +:+ bs


class Unappend as where
  unappend :: List (as +:+ bs) -> (List as, List bs)

instance Unappend '[] where
  unappend bs = (Nil, bs)

instance Unappend as => Unappend (a ': as) where
  unappend (a ::- abs) = case unappend abs of (as, bs) -> (a ::- as, bs)

---------------------------------
-- Operations to transform output
-- Preliminary apply class

class Apply f a b where
  apply :: f -> a -> b


-- Map
class MapL f xs ys where
  mapL :: f -> List xs -> List ys

instance MapL f '[] '[] where
  mapL _ _ = Nil


instance (Apply f x y, MapL f xs ys)
  => MapL f (x ': xs) (y ': ys) where
  mapL f (x ::- xs) = apply f x ::- mapL f xs

-- Foldr
class FoldrL f acc xs where
  foldrL :: f -> acc -> List xs -> acc

instance FoldrL f acc '[] where
  foldrL _ acc _ = acc

instance (Apply f x (acc -> acc), FoldrL f acc xs)
  => FoldrL f acc (x ': xs) where
  foldrL f acc (x ::- xs) = apply f x $ foldrL f acc xs

type family ConstMap (t :: *) (xs :: [*]) :: [*] where
  ConstMap _      '[]  = '[]
  ConstMap t (x ': xs) = t ': (ConstMap t xs)

----------------------------------------
-- Features to ease feeding back outputs
--
class Applicative m => SequenceList m a b | a -> b, m b -> a where
    sequenceListA :: List a -> m (List b)

instance Applicative m => SequenceList m '[] '[] where
    sequenceListA _ = pure Nil

instance (Applicative m, SequenceList m as bs) => SequenceList m (m a ': as) (a ': bs) where
    sequenceListA (a ::- b) = liftA2 (::-) a (sequenceListA b)

--------------------------------------------------------------------------------

class Monad m => TraverseList_ (ctx :: * -> Constraint) m a where
  traverseList_
    :: Proxy ctx
     -> (forall x. ctx x => x -> m ())
    -> List a
    -> m ()

instance Monad m => TraverseList_ ctx m '[] where
  traverseList_ _proxy _f _ = pure ()

instance (ctx a, Monad m, TraverseList_ ctx m as)
       => TraverseList_ ctx m (m a ': as) where
  traverseList_ proxy f (a ::- b) = do
    x <- a
    f x
    xs <- traverseList_ proxy f b
    pure ()

-- Indexing on the list

data Nat = Z | S Nat

data Natural a where
  Zero :: Natural 'Z
  Succ :: Natural a -> Natural ('S a)


class IndexList (n :: Nat) (xs :: [Type]) (i :: Type) | n xs -> i where
   fromIndex :: Natural n -> List xs -> i

instance IndexList Z (x ': xs) x where
   fromIndex Zero (x ::- _) = x

instance IndexList n xs a => IndexList (S n) (x ': xs) a where
   fromIndex (Succ n) (_ ::- xs) = fromIndex n xs


--------------------------------------
-- List functionality

headL :: List (a ': as) -> a
headL (x ::- _) = x

tailL :: List (a ': as) -> List as
tailL (_ ::- xs) = xs

type family LastL xs where
  LastL '[x] = x
  LastL (x ': xs) = LastL xs

lastL :: List a -> LastL a
lastL (x ::- Nil)          = x
lastL (x ::- xs@(_ ::- _)) = lastL xs
lastL Nil = error "impossible, stop bothering me with the warning"

--------------------------------------------------------------------------------
-- Open games

data OpenGame o c a b x s y r = OpenGame {
  play :: List a -> o x s y r,
  evaluate :: List a -> c x s y r -> List b
}

lift :: o x s y r -> OpenGame o c '[] '[] x s y r
lift o = OpenGame {
  play = \Nil -> o,
  evaluate = \Nil _ -> Nil
}

reindex :: (List a -> List a') -> (List a -> List b' -> List b)
        -> OpenGame o c a' b' x s y r -> OpenGame o c a b x s y r
reindex v u g = OpenGame {
  play = \a -> play g (v a),
  evaluate = \a c -> u a (evaluate g (v a) c)
}

(>>>) :: (Optic o, Context c o, Unappend a, Unappend b)
      => OpenGame o c a b x s y r -> OpenGame o c a' b' y r z q
      -> OpenGame o c (a +:+ a') (b +:+ b') x s z q
(>>>) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a >>>> play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (cmap identity (play h a') c)
                                                  +:+ evaluate h a' (cmap (play g a) identity c)
}

(&&&) :: (Optic o, Context c o, Unappend a, Unappend b, Show x, Show x')
      => OpenGame o c a b x s y r -> OpenGame o c a' b' x' s' y' r'
      -> OpenGame o c (a +:+ a') (b +:+ b') (x, x') (s, s') (y, y') (r, r')
(&&&) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a &&&& play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (play h a' \\ c)
                                                  +:+ evaluate h a' (play g a // c)
}

--------------------------------------------------------------------------------
-- Optic class

class Optic o where
  lens :: (s -> a) -> (s -> b -> t) -> o s t a b
  (>>>>) :: o s t a b -> o a b p q -> o s t p q
  (&&&&) :: o s1 t1 a1 b1 -> o s2 t2 a2 b2 -> o (s1, s2) (t1, t2) (a1, a2) (b1, b2)
  (++++) :: o s1 t a1 b -> o s2 t a2 b -> o (Either s1 s2) t (Either a1 a2) b

identity :: (Optic o) => o s t s t
identity = lens id (flip const)

class Precontext c where
  void :: c () () () ()

-- Precontext is a separate class to Context because otherwise the typechecker throws a wobbly

class (Optic o, Precontext c) => Context c o where
  cmap :: o s1 t1 s2 t2 -> o a1 b1 a2 b2 -> c s1 t1 a2 b2 -> c s2 t2 a1 b1
  (//) :: (Show s1) => o s1 t1 a1 b1 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s2 t2 a2 b2
  (\\) :: (Show s2) => o s2 t2 a2 b2 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s1 t1 a1 b1

-- (\\) is derivable from (//) using
-- l \\ c = l // (cmap (lift swap swap) (lift swap swap) c)
-- (and vice versa) but it doesn't typecheck and I don't understand why

-- ContextAdd is a separate class to Precontext and Context because its implementation is more ad-hoc,
-- eg. it can't be done generically in a monad

class ContextAdd c where
  prl :: c (Either s1 s2) t (Either a1 a2) b -> Maybe (c s1 t a1 b)
  prr :: c (Either s1 s2) t (Either a1 a2) b -> Maybe (c s2 t a2 b)

-------------------------------------------------------------
--- replicate the old implementation of a stochastic context
type Stochastic = T Double
type Vector = HM.Map String Double

-- Experimental non Stochastic
-- Same as used in learning implementation
-- Can be used for IO as well
data MonadOptic s t a b where
  MonadOptic :: (s -> RIO Rdr (z, a))
             -> (z -> b -> StateT Vector (RIO Rdr) t)
             -> MonadOptic s t a b

instance Optic MonadOptic where
  lens v u = MonadOptic (\s -> return (s, v s)) (\s b -> return (u s b))
  (>>>>) (MonadOptic v1 u1) (MonadOptic v2 u2) = MonadOptic v u
    where v s = do {(z1, a) <- v1 s; (z2, p) <- v2 a; return ((z1, z2), p)}
          u (z1, z2) q = do {b <- u2 z2 q; u1 z1 b}
  (&&&&) (MonadOptic v1 u1) (MonadOptic v2 u2) = MonadOptic v u
    where v (s1, s2) = do {(z1, a1) <- v1 s1; (z2, a2) <- v2 s2; return ((z1, z2), (a1, a2))}
          u (z1, z2) (b1, b2) = do {t1 <- u1 z1 b1; t2 <- u2 z2 b2; return (t1, t2)}
  (++++) (MonadOptic v1 u1) (MonadOptic v2 u2) = MonadOptic v u
    where v (Left s1)  = do {(z1, a1) <- v1 s1; return (Left z1, Left a1)}
          v (Right s2) = do {(z2, a2) <- v2 s2; return (Right z2, Right a2)}
          u (Left z1) b  = u1 z1 b
          u (Right z2) b = u2 z2 b

data MonadContext s t a b where
  MonadContext :: (Show z) => (RIO Rdr) (z, s) -> (z -> a -> StateT Vector (RIO Rdr) b) -> MonadContext s t a b

instance Precontext MonadContext where
  void = MonadContext (return ((), ())) (\() () -> return ())

instance Context MonadContext MonadOptic where
  cmap (MonadOptic v1 u1) (MonadOptic v2 u2) (MonadContext h k)
            = let h' = do {(z, s) <- h; (_, s') <- v1 s; return (z, s')}
                  k' z a = do {(z', a') <- Trans.lift (v2 a); b' <- k z a'; u2 z' b'}
               in MonadContext h' k'
  (//) (MonadOptic v u) (MonadContext h k)
            = let h' = do {(z, (s1, s2)) <- h; return ((z, s1), s2)}
                  k' (z, s1) a2 = do {(_, a1) <- Trans.lift (v s1); (_, b2) <- k z (a1, a2); return b2}
               in MonadContext h' k'
  (\\) (MonadOptic v u) (MonadContext h k)
            = let h' = do {(z, (s1, s2)) <- h; return ((z, s2), s1)}
                  k' (z, s2) a1 = do {(_, a2) <- Trans.lift (v s2); (b1, _) <- k z (a1, a2); return b1}
               in MonadContext h' k'


--------------------------------------------------------------------------------
-- Dependent decision IO

type IOOpenGame a b x s y r = OpenGame MonadOptic MonadContext a b x s y r

dependentDecisionIO
  :: forall x. Show x => String
  -> Int
  -> [ActionPD]
  -> IOOpenGame '[Kleisli CondensedTableV x ActionPD] '[(RIO Rdr) (Diagnostics ActionPD)] x () ActionPD Double
dependentDecisionIO name sampleSize ys = OpenGame { play, evaluate} where

  play :: List '[Kleisli CondensedTableV x ActionPD]
       -> MonadOptic x () ActionPD Double
  play (strat ::- Nil) =
    MonadOptic v u

    where
      v x = do
        g <- newStdGen
        gS <- newIOGenM g
        action <- genFromTable (runKleisli strat x) gS
        glog (VChooseAction action)
        -- logstr (name ++ take 1 (show action))
        return ((),action)

      u () r = modify (adjustOrAdd (+ r) r name)

  evaluate :: List '[Kleisli CondensedTableV x ActionPD]
           -> MonadContext x () ActionPD Double
           -> List '[(RIO Rdr) (Diagnostics ActionPD)]  ----     <-- do this next
  evaluate (strat ::- Nil) (MonadContext h k) =
    output ::- Nil

    where

      output =
        mapRIO (contramap (AsPlayer name)) $ do
        glog Outputting
        samplePayoffs' <- mapRIO (contramap SamplePayoffs) samplePayoffs
        averageUtilStrategy' <- mapRIO (contramap AverageUtility) averageUtilStrategy
        return  Diagnostics{
            playerName = name
          , averageUtilStrategy = averageUtilStrategy'
          , samplePayoffs = samplePayoffs'
          , currentMove = 0
          }

        where
          -- Sample the average utility from all actions
          samplePayoffs = do -- newline
                             -- logln (name ++ ": samplePayoffs")
                             -- indent
                             vs <- mapM sampleY ys
                             -- deindent
                             pure vs
            where
              -- Sample the average utility from a single action
               sampleY :: ActionPD -> RIO (GLogFunc SamplePayoffsMsg) Double
               sampleY y = do
                  glog (SampleAction y)
                  -- newline
                  -- logln (name ++ ": sampleY: " ++ show y)
                  -- indent
                  ls1 <- mapM (\i -> do -- newline
                                        -- logstr ("[" ++ printf "%3i" i ++ "]  ")
                                        -- indent
                                        v <- mapRIO (contramap (SampleRootMsg i)) $ u y
                                        -- logstr (" => " ++ show v)
                                        -- deindent
                                        pure v) [1..sampleSize]
                  -- newline
                  let average =  (sum ls1 / fromIntegral sampleSize)
                  glog (SampleAverageIs average)
                  -- newline
                  -- logstr ("average=" ++ show average)

                  -- deindent
                  pure average

          -- Sample the average utility from current strategy
          averageUtilStrategy = do
            glog StartingAverageUtil
            -- newline
            -- newline
            -- logstr "averageUtilStrategy"
            -- indent
            -- newline
            -- newline

            -- logstr "h'["
            (_,x) <- mapRIO (contramap AverageRootMsg) h
            -- logstr "]"
            -- newline
            -- logstr ("x=" ++ show x)
            -- newline
            g <- newStdGen
            gS <- newIOGenM g
            -- logstr "actions"
            -- indent
            -- newline
            -- newline
            actionLS' <- mapM (\i -> do
                                        v <- mapRIO (contramap AverageRootMsg) $ action x gS
                                        glog (AverageActionChosen v)
                                        -- logstr (take 1 (show v))
                                        pure v)
                             [1.. sampleSize]
            -- deindent
            -- newline
            -- newline
            -- logstr "utils"
            -- indent
            utilLS  <- mapM (\(i,a) ->
                                   do -- newline
                                      -- logstr ("[" ++ printf "%3i %s" i (take 1 $ show a) ++ "] ")
                                      glog (AverageIterAction i a)
                                      v <- mapRIO (contramap AverageRootMsg) $ u a
                                      -- logstr (" => " ++ show v)
                                      pure v
                             )
                        (zip [1 :: Int ..] actionLS')


            -- newline
            -- deindent
            -- newline
            let average = (sum utilLS / fromIntegral sampleSize)
            -- logstr ("average=" ++ show average)
            glog (AverageComplete average)
            -- deindent
            -- newline

            return average

            where action x gS = do
                    genFromTable (runKleisli strat x) gS

          u y = do
             glog UStart
             -- logstr "u["
             -- logstr "h["
             (z,_) <- mapRIO (contramap WithinU) h
             -- logstr "]"
             v <-
              mapRIO (contramap CalledK) $
              evalStateT (do -- Trans.lift $ logstr "k["
                             r <-  k z y
                             -- Trans.lift $ logstr "]"
                             mp <- gets id
                             -- Trans.lift $ case HM.lookup name mp of
                             --   Nothing -> logstr "!"
                             --   Just{} -> logstr "@"
                             gets ((+ r) . HM.findWithDefault 0.0 name))
                          HM.empty
             -- logstr "]"
             glog UEnd
             pure v
-- Support functionality for constructing open games
fromLens :: (x -> y) -> (x -> r -> s) -> IOOpenGame '[] '[] x s y r
fromLens v u = OpenGame {
  play = \Nil -> MonadOptic (\x -> return (x, v x)) (\x r -> return (u x r)),
  evaluate = \Nil _ -> Nil}


fromFunctions :: (x -> y) -> (r -> s) -> IOOpenGame '[] '[] x s y r
fromFunctions f g = fromLens f (const g)



-- discount Operation for repeated structures
discount :: String -> (Double -> Double) -> IOOpenGame '[] '[] () () () ()
discount name f = OpenGame {
  play = \_ -> let v () = return ((), ())
                   u () () = modify (adjustOrAdd f (f 0) name)
                 in MonadOptic v u,
  evaluate = \_ _ -> Nil}

deviationsInContext :: (Show a, Ord a)
                    =>  Agent -> a -> (a -> (RIO Rdr) Double) -> [a] -> (RIO Rdr) [DiagnosticInfoIO a]
deviationsInContext name strategy u ys = do
     ls              <- mapM u ys
     strategicPayoff <- u strategy
     let zippedLs    =  zip ys ls
         (optimalPlay, optimalPayoff) = maximumBy (comparing snd) zippedLs
     pure [ DiagnosticInfoIO
            {  playerIO = name
            , optimalMoveIO = optimalPlay
            , optimalPayoffIO = optimalPayoff
            , currentMoveIO   = strategy
            , currentPayoffIO = strategicPayoff
            , otherActions = [] -- TODO: !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
            }]

data DiagnosticInfoIO y = DiagnosticInfoIO
  { playerIO          :: String
  , optimalMoveIO     :: y
  , optimalPayoffIO   :: Double
  , currentMoveIO     :: y
  , currentPayoffIO   :: Double
  , otherActions      :: [Double]
  } deriving Show

type Agent = String

data Diagnostics y = Diagnostics {
  playerName :: String
  , averageUtilStrategy :: Double
  , samplePayoffs :: [Double]
  , currentMove :: Double
  }
  deriving (Show)

--------------------------------------------------------------------------------
-- Instance of a game

--------------------------------------------------------------------------------
-- Entry points

-- printOutput 20 (transformStratTuple strategyTupleTest) (Cooperate,Cooperate)
-- Own util 1
-- 45.296
-- Other actions
-- [43.957,45.309]
-- Own util 2
-- 44.944
-- Other actions
-- [44.415,45.746]

printOutput
  :: Integer
     -> List
          '[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
            Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
     -> (ActionPD, ActionPD)
     -> IO ()
printOutput iterator strat initialAction = do
  indentRef <- newIORef 0
  runRIO (mkGLogFunc logFuncTracing) $ do
    let resultIOs@(result1 ::- result2 ::- Nil) = repeatedPDEq iterator strat initialAction
    traverseList_ (Proxy :: Proxy Show) (liftIO . print) resultIOs
    pure ()

-- ignore this one
logFuncTracing _ (AsPlayer _ (SamplePayoffs (SampleRootMsg _ (CalledK {})))) = pure ()
logFuncTracing _ (AsPlayer _ (AverageUtility (AverageRootMsg (CalledK {})))) = pure ()
logFuncTracing callStack msg = do
  case getCallStack callStack of
     [("glog", srcloc)] -> do
       fp <- makeRelativeToCurrentDirectory (srcLocFile srcloc)
       S8.putStrLn (S8.pack (prettySrcLoc0 (srcloc{srcLocFile=fp}) ++ show msg))

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

repeatedPDEq
  :: Integer
     -> List
          '[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
            Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
     -> (ActionPD, ActionPD)
     -> List
          '[(RIO Rdr) (Diagnostics ActionPD), (RIO Rdr) (Diagnostics ActionPD)]
repeatedPDEq  iterator strat initialAction =
  evaluate prisonersDilemmaCont strat context
  where context  = contextCont iterator strat initialAction
        -- fix context used for the evaluation
          where contextCont  iterator strat initialAction =
                  MonadContext
                    (pure ((),initialAction))
                    (\_ action -> determineContinuationPayoffsIO
                                    iterator strat action)

strategyTupleTest = stageStrategyTest ::- stageStrategyTest ::- Nil

-- | Classic stochastic definition: equal chance of cooperate/defect.
stageStrategyTest :: Kleisli Stochastic (ActionPD, ActionPD) ActionPD
stageStrategyTest = Kleisli $ const $ distFromList [(Cooperate, 0.5),(Defect, 0.5)]

distFromList :: [(a, Double)] -> T Double a
distFromList = fromFreqs

--------------------------------------------------------------------------------
-- Transforming Stochastic to CondensedTableV

transformStratTuple :: List
                        '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                          Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                    -> List
                        '[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                          Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
transformStratTuple (x ::- y ::- Nil) =
  transformStrat x
  ::- transformStrat y
  ::- Nil

  where

    transformStrat strat = Kleisli (\x ->
      let y = runKleisli strat x
          ls = decons y
          v = V.fromList ls
          in tableFromProbabilities v)

---------------------------------------------
-- Contains a first, very, very shaky version
-- that does Monte Carlo through the evaluate
---------------------------------------------

discountFactor :: Double
discountFactor = 1.0

prisonersDilemmaCont :: OpenGame
                          MonadOptic
                          MonadContext
                          ('[Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                             Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD])
                          ('[(RIO Rdr) (Diagnostics ActionPD), (RIO Rdr) (Diagnostics ActionPD)])
                          (ActionPD, ActionPD)
                          ()
                          (ActionPD, ActionPD)
                          ()


prisonersDilemmaCont = [opengame|

   inputs    : (dec1Old,dec2Old) ;
   feedback  :      ;

   :----------------------------:
   inputs    :  (dec1Old,dec2Old)    ;
   feedback  :      ;
   operation : dependentDecisionIO "1" 100 [Cooperate,Defect];
   outputs   : decisionPlayer1 ;
   returns   : prisonersDilemmaMatrix decisionPlayer1 decisionPlayer2 ;

   inputs    :   (dec1Old,dec2Old)   ;
   feedback  :      ;
   operation : dependentDecisionIO "2" 100 [Cooperate,Defect];
   outputs   : decisionPlayer2 ;
   returns   : prisonersDilemmaMatrix decisionPlayer2 decisionPlayer1 ;

   operation : discount "1" (\x -> x * discountFactor) ;

   operation : discount "2" (\x -> x * discountFactor) ;

   :----------------------------:

   outputs   : (decisionPlayer1,decisionPlayer2)     ;
   returns   :      ;
  |]

--------------------------------
-- This is for the mixed setting
-- which includes the Bayesian setup
-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffs :: Integer
                             -> List
                                      '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                        Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                             -> (ActionPD,ActionPD)
                             -> StateT Vector (RIO Rdr) ()
determineContinuationPayoffs 1        _ _ = pure ()
determineContinuationPayoffs iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffs (pred iterator) strat nextInput
 where executeStrat =  play prisonersDilemmaCont (transformStratTuple strat)


sampleDetermineContinuationPayoffs :: Int
                                  -- ^ Sample size
                                  -> Integer
                                  -- ^ How many rounds are explored?
                                  -> List
                                            '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
                                              Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
                                  -> (ActionPD,ActionPD)
                                  -> StateT Vector (RIO Rdr) ()
sampleDetermineContinuationPayoffs sampleSize iterator strat initialValue = do
  replicateM_ sampleSize (determineContinuationPayoffs iterator strat initialValue)
  v <- ST.get
  ST.put (average sampleSize v)

-- -- NOTE EVIL EVIL
-- _sampleDetermineContinuationPayoffsStoch :: Int
--                                   -- ^ Sample size
--                                   -> Integer
--                                   -- ^ How many rounds are explored?
--                                   -> List
--                                             '[Kleisli Stochastic (ActionPD, ActionPD) ActionPD,
--                                               Kleisli Stochastic (ActionPD, ActionPD) ActionPD]
--                                   -> (ActionPD,ActionPD)
--                                   -> StateT Vector Stochastic ()
-- _sampleDetermineContinuationPayoffsStoch sampleSize iterator strat initialValue = do
--    transformStateTIO $  sampleDetermineContinuationPayoffs sampleSize iterator strat initialValue
--    where
--       transformStateTIO ::  StateT Vector (RIO Rdr) () ->  StateT Vector Stochastic ()
--       transformStateTIO sTT = StateT (\s -> unsafeTransformIO $  ST.runStateT sTT s)
--       unsafeTransformIO :: (RIO Rdr) a -> Stochastic a
--       unsafeTransformIO a =
--         let a' = unsafePerformIO (runa
--             in certainly a'

-----------------------------
-- For IO only
-- determine continuation for iterator, with the same repeated strategy
determineContinuationPayoffsIO :: Integer
                               -> List
                                     [Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD,
                                     Kleisli CondensedTableV (ActionPD, ActionPD) ActionPD]
                               -> (ActionPD,ActionPD)
                               -> StateT Vector (RIO Rdr) ()
determineContinuationPayoffsIO 1       _strat _action = pure ()
determineContinuationPayoffsIO iterator strat action = do
   extractContinuation executeStrat action
   nextInput <- ST.lift $ extractNextState executeStrat action
   determineContinuationPayoffsIO (pred iterator) strat nextInput
 where executeStrat =  play prisonersDilemmaCont strat

----------------------------------------------------
-- This is taken from the other MonteCarloTest setup
-- Needs to be transformed in order to be tested

-- extract continuation
extractContinuation :: MonadOptic s () a () -> s -> StateT Vector (RIO Rdr) ()
extractContinuation (MonadOptic v u) x = do
  (z,_) <- ST.lift (v x)
  u z ()

-- extract next state (action)
extractNextState :: MonadOptic s () a () -> s -> (RIO Rdr) a
extractNextState (MonadOptic v _) x = do
  (_,a) <- v x
  pure a

--------------------------------------------------------------------------------
-- SimultaneousMoves

-- 1.0. Prisoner's dilemma
data ActionPD = Cooperate | Defect
  deriving (Eq, Ord, Show)

-- | Payoff matrix for player i given i's action and j's action
prisonersDilemmaMatrix :: ActionPD -> ActionPD -> Double
prisonersDilemmaMatrix Cooperate Cooperate   = 3
prisonersDilemmaMatrix Cooperate Defect  = 0
prisonersDilemmaMatrix Defect Cooperate  = 5
prisonersDilemmaMatrix Defect Defect = 1
