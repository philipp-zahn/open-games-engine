module Engine.OpticClass 

import Data.TriState
import Control.Monad.State

infixr 5 //, \\
infixr 8 >>>>
infixl 7 &&&&
infixl 6 ++++

public export
interface Optic (o : Type -> Type -> Type -> Type -> Type) where
  lens : {s : Type} -> (s -> a) -> (s -> b -> t) -> o s t a b
  (>>>>) : o s t a b -> o a b p q -> o s t p q
  (&&&&) : o s1 t1 a1 b1 -> o s2 t2 a2 b2 -> o (s1, s2) (t1, t2) (a1, a2) (b1, b2)
  (++++) : {s1, s2 : Type} -> o s1 t a1 b -> o s2 t a2 b -> o (Either s1 s2) t (Either a1 a2) b

interface ContextAdd (c : Type -> Type -> Type -> Type -> Type) where
  match : c (Either x1 x2) s (Either y1 y2) r
       -> TriState (c x1 s y1 r) (c x2 s y2 r)

interface Precontext (c : Type -> Type -> Type -> Type -> Type) where
  cUnit : c () () () ()

interface (Optic o) => Context (c, o : Type -> Type -> Type -> Type -> Type) where
  cmap : o s1 t1 s2 t2 -> o a1 b1 a2 b2 -> c s1 t1 a2 b2 -> c s2 t2 a1 b1
  (//) : o s1 t1 a1 b1 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s2 t2 a2 b2
  (\\) : o s2 t2 a2 b2 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s1 t1 a1 b1
  both : o s1 t1 a1 b1 -> o s2 t2 a2 b2 
      -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> (c s2 t2 a2 b2, c s1 t1 a1 b1)
  both g1 g2 c = (g1 // c, g2 \\ c)

-------------------------------------------------------------
--- replicate the old implementation of a stochastic context

  
Vector : Type
Vector = String -> Double

parameters (Stochastic : Type -> Type) {auto ms : Monad Stochastic}
  
  record StochasticStatefulOptic (s, t, a, b : Type) where
      constructor MkStochasticStatefulOptic 
      {residual : Type}
      view : (s -> Stochastic (residual, a))
      update : (residual -> b -> StateT Vector Stochastic t)
  
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
  
  
  record StochasticStatefulContext (s, t, a, b : Type) where
    constructor MkStochasticStatefulContext 
    {z : Type} 
    {auto showInstance : Show z} 
    view : Stochastic (z, s) 
    update : z -> a -> StateT Vector Stochastic b 
  
  implementation Precontext StochasticStatefulContext where
    cUnit = MkStochasticStatefulContext {z=Unit} 
              (pure ((), ())) (\(), () => pure ()) 
  
  implementation Context StochasticStatefulContext StochasticStatefulOptic where
    cmap (MkStochasticStatefulOptic v1 u1) (MkStochasticStatefulOptic v2 u2) (MkStochasticStatefulContext h k)
              = MkStochasticStatefulContext 
                   (do {(z, s) <- h; (_, s') <- v1 s; pure (z, s')})
                   (\z, a => do {(z', a') <- lift (v2 a); b' <- k z a'; u2 z' b'})
    (//) (MkStochasticStatefulOptic v u) (MkStochasticStatefulContext h k)
              = 
               --(do {(z, (s1, s2)) <- h; pure ((z, s1), s2)})
                   ?le -- (\(z, s1), a2 => do {(_, a1) <- lift (v s1); (_, b2) <- k z (a1, a2); pure b2})
    (\\) (MkStochasticStatefulOptic v u) (MkStochasticStatefulContext h k)
              = MkStochasticStatefulContext
                   ?ad --(do {(z, (s1, s2)) <- h; pure ((z, s2), s1)})
                   ?re -- (\(z, s2), a1 => do {(_, a2) <- lift (v s2); (b1, _) <- k z (a1, a2); pure b1})
  
    {-
  instance ContextAdd StochasticStatefulContext where
    prl (StochasticStatefulContext h k)
      = let fs = [((z, s1), p) | ((z, Choice1 s1), p) <- decons h]
         in if null fs then None
                       else Some (StochasticStatefulContext (fromFreqs fs) (\z a1 -> k z (Choice1 a1)))
    prr (StochasticStatefulContext h k)
      = let fs = [((z, s2), p) | ((z, Choice2 s2), p) <- decons h]
         in if null fs then None
                       else Some (StochasticStatefulContext (fromFreqs fs) (\z a2 -> k z (Choice2 a2)))
  
  {-
  -}
