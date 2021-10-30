module Engine.OpticClass 

import Data.TriState
import Data.SortedMap
import Control.Monad.State
import public Numeric.Probability.Distribution

infixr 5 //, \\
infixr 8 >>>>
infixl 7 &&&&
infixl 6 ++++

public export
interface Optic (0 o : Type -> Type -> Type -> Type -> Type) where
  lens : {0 s : Type} -> (s -> a) -> (s -> b -> t) -> o s t a b
  (>>>>) : o s t a b -> o a b p q -> o s t p q
  (&&&&) : o s1 t1 a1 b1 -> o s2 t2 a2 b2 -> o (s1, s2) (t1, t2) (a1, a2) (b1, b2)
  (++++) : {0 s1, s2 : Type} -> o s1 t a1 b -> o s2 t a2 b -> o (Either s1 s2) t (Either a1 a2) b

public export
interface ContextAdd (0 c : Type -> Type -> Type -> Type -> Type) where
  match : c (Either x1 x2) s (Either y1 y2) r
       -> TriState (c x1 s y1 r) (c x2 s y2 r)

export
interface Precontext (0 c : Type -> Type -> Type -> Type -> Type) where
  cUnit : c () () () ()

public export
interface (Optic o) => Context (0 c, o : Type -> Type -> Type -> Type -> Type) where
  cmap : o s1 t1 s2 t2 -> o a1 b1 a2 b2 -> c s1 t1 a2 b2 -> c s2 t2 a1 b1
  (//) : Show s1 => o s1 t1 a1 b1 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s2 t2 a2 b2
  (\\) : Show s2 => o s2 t2 a2 b2 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s1 t1 a1 b1
  both : Show s1 => Show s2 => o s1 t1 a1 b1 -> o s2 t2 a2 b2 
      -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> (c s2 t2 a2 b2, c s1 t1 a1 b1)
  both g1 g2 c = (g1 // c, g2 \\ c)

-------------------------------------------------------------
--- replicate the old implementation of a stochastic context

public export
Vector : Type
Vector = String -> Double


public export
Stochastic : Type -> Type
Stochastic = T Double

public export
record StochasticStatefulOptic (s, t, a, b : Type) where
    constructor MkStochasticStatefulOptic 
    {0 residual : Type}
    view : (s -> Stochastic (residual, a))
    update : (residual -> b -> StateT Vector Stochastic t)

export
implementation Optic StochasticStatefulOptic where
  lens v u {s} = MkStochasticStatefulOptic {residual=s} (\arg => pure (arg, v arg)) (\s, b => pure (u s b)) 
  (MkStochasticStatefulOptic {residual=r1} v1 u1) >>>> (MkStochasticStatefulOptic {residual=r2} v2 u2) = 
    MkStochasticStatefulOptic (\s => do (z1, a) <- v1 s
                                        (z2, p) <- v2 a
                                        pure ((z1, z2), p)) 
                              (\x, q => u1 (fst x) !(u2 (snd x) q))
  (MkStochasticStatefulOptic v1 u1) &&&& (MkStochasticStatefulOptic v2 u2) = 
    MkStochasticStatefulOptic (\s => do { (z1, a1) <- v1 (fst s)
                                        ; (z2, a2) <- v2 (snd s)
                                        ; pure ((z1, z2), (a1, a2))}) 
                              (\z, b => do {t1 <- u1 (fst z) (fst b); t2 <- u2 (snd z) (snd b); pure (t1, t2)})
  (MkStochasticStatefulOptic {residual=r1} v1 u1) ++++ 
  (MkStochasticStatefulOptic {residual=r2} v2 u2) = 
    MkStochasticStatefulOptic {residual=Either r1 r2}
      (\case (Left x) => do {(z1, a1) <- v1 x; pure (Left z1, Left a1)}
             (Right x) => do {(z2, a2) <- v2 x; pure (Right z2, Right a2)}) 
      (\case (Left x) => u1 x
             (Right x) => u2 x)

public export
record StochasticStatefulContext (s, t, a, b : Type) where
  constructor MkStochasticStatefulContext 
  {0 z : Type} 
  {auto showInstance : Show z} 
  view : Stochastic (z, s) 
  update : z -> a -> StateT Vector Stochastic b 

export
implementation Precontext StochasticStatefulContext where
  cUnit = MkStochasticStatefulContext {z=Unit} 
            (pure ((), ())) (\(), () => pure ()) 

public export
implementation Context StochasticStatefulContext StochasticStatefulOptic where
  cmap (MkStochasticStatefulOptic v1 u1) (MkStochasticStatefulOptic v2 u2) (MkStochasticStatefulContext h k)
            = MkStochasticStatefulContext 
                 (do {(z, s) <- h; (_, s') <- v1 s; pure (z, s')})
                 (\z, a => do {(z', a') <- lift (v2 a); b' <- k z a'; u2 z' b'})
  (//) (MkStochasticStatefulOptic v u) (MkStochasticStatefulContext h k)
            = MkStochasticStatefulContext
                (do {(z, (s1, s2)) <- h; pure ((z, s1), s2)})
                (\(z, s1), a2 => do {(_, a1) <- lift (v s1); (_, b2) <- k z (a1, a2); pure b2})
  (\\) (MkStochasticStatefulOptic v u) (MkStochasticStatefulContext {z=z2} h k)
            = MkStochasticStatefulContext --{z=(z2, s1)} 
                (do {(z, (s1, s2)) <- h; pure ((z, s2), s1)}) 
                (\(z, s2), a1 => do {(_, a2) <- lift (v s2); (b1, _) <- k z (a1, a2); pure b1})

partition' : (a -> Either b c) -> List a -> (List b, List c)
partition' p []      = ([], [])
partition' p (x::xs) =
  let (lefts, rights) = partition' p xs in
    case p x of
      Left x => (x::lefts, rights)
      Right x => (lefts, x::rights)

public export
implementation ContextAdd StochasticStatefulContext where
  match (MkStochasticStatefulContext h k) 
      = case partition' (\case ((a, Left x), y) => Left ((a, x), y)
                               ((a, Right x), y) => Right ((a, x), y)) h.decons of
             (a, []) => Choice1 (MkStochasticStatefulContext (fromFreqs a) (\z, a1 => k z (Left a1)))
             ([], b) => Choice2 (MkStochasticStatefulContext (fromFreqs b) (\z, a2 => k z (Right a2)))
             (a, b)  => Both (MkStochasticStatefulContext (fromFreqs a) (\z, a1 => k z (Left a1)))
                             (MkStochasticStatefulContext (fromFreqs b) (\z, a2 => k z (Right a2)))

{-
-}
