module P where
import           Control.Monad
import           Control.Monad.State
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Numeric.Probability.Distribution
import           System.Random.MWC.CondensedTable
import           System.Random.Stateful

newtype ProbT m e a = ProbT
  { runProbT :: StateT (CondensedTableV e, StdGen) m a
  }
instance Monad m => Functor (ProbT m e) where fmap = liftM
instance Monad m => Applicative (ProbT m e) where pure = return; (<*>) = ap
instance Monad m => Monad (ProbT m e) where
  return = ProbT . return
  (>>=) m f =
    ProbT
      (do (table, gen) <- get
          let (a, g) = runStateGen gen (genFromTable table)
          -- In 'probability' they combine probabilities here. But,
          -- perhaps instead you could combine them... (see below) and
          -- then this monad instance is deleted, and just derived
          -- from State.
          undefined)

uniform :: Monad m => Vector (e, Double) -> ProbT m e e
uniform vs = do
  setUniform vs
  draw

-- ... Perhaps you could combine them here?
setUniform :: Monad m => Vector (e, Double) -> ProbT m e ()
setUniform vs = ProbT (modify (\(s,g) -> (tableFromProbabilities vs,g)))

draw :: Monad m => ProbT m e e
draw =
  ProbT
    (do (table, gen) <- get
        let (e, g) = runStateGen gen (genFromTable table)
        pure e)

-- Finally, you need a `decons', such as,
decons :: ProbT m e () -> m [(e,Double)]
decons = undefined
-- ... and perhaps an internal CTable would do the trick for this. But
-- what is the project doing with the resulting list? Good question to
-- ask.
--
-- data CTable a = CTable
--   { ctable :: !(CondensedTableV a)
--   , population :: !(V.Vector (a,Double))
--   }
