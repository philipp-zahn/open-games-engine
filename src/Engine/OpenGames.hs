{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Engine.OpenGames
 ( OpenGame(..)
 , lift
 , reindex
 , (>>>)
 , (&&&)
 ) where


import Engine.OpticClass
import Engine.TLL
import Data.Type.Equality ((:~:)(..))

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
omap :: Optic o =>
        (s -> s') ->
        (x' -> x) ->
        (y -> y') ->
        (r' -> r) ->
        o x s y r -> o x' s' y' r'
omap g g1 g2 g3 optic = lens g1 (const g) >>>> (optic >>>> lens g2 (const g3) )

gmap :: forall c o a b s s' x x' y y' r r'. (Optic o, Context c o) =>
        (s -> s') ->
        (x' -> x) ->
        (y -> y') ->
        (r' -> r) ->
        OpenGame o c a b x s y r ->
        OpenGame o c a b x' s' y' r'
gmap f1 f2 f3 f4 (OpenGame p e) =
    OpenGame (\t -> omap f1 f2 f3 f4 (p t))
             (\t b -> e t (cmap @c @o (lens f2 (const f1)) (lens f3 (const f4)) b))


pop1 :: forall o c a b x s y r. (Optic o, Context c o) => OpenGame o c a b x s y r ->
  OpenGame o c (CatRepeat (S Z) a) (CatRepeat (S Z) b)
           (Vec (S Z) x) (Vec (S Z) s) (Vec (S Z) y) (Vec (S Z) r)
pop1 game =
  let v = gmap mkVec (vecHead @Z) mkVec (vecHead @Z) game
   in case repeat1Proof @a of
        Refl -> case repeat1Proof @b of Refl -> v

split :: Vec (S n) a -> (a, Vec n a)
split (x :> xs) = (x, xs)

stick :: (a, Vec n a) -> Vec (S n) a
stick (x, xs) = x :> xs

population :: forall o c a b x s y r n.
  (Optic o, Context c o, Unappend a, Unappend b, Show x) => Natural n ->
  (Vec (S n) (OpenGame o c a b x s y r)) ->
  OpenGame o c (CatRepeat (S n) a) (CatRepeat (S n) b)
               (Vec (S n) x) (Vec (S n) s) (Vec (S n) y) (Vec (S n) r)
population Zero (v :> Empty) = pop1 v
population (Succ n) (v :> v' :> vs) =
  let ind = population n (v' :> vs) in
      OpenGame (\ls -> case repeatSuccProof @n @a of
                            Refl -> let (xs, ys) = unappend @a ls
                                        p1 = play v xs
                                        p2 = play ind ys in
                                        omap stick split stick split (p1 &&&& p2))
               (\ls b ->
                 case repeatSuccProof of
                   Refl -> let (xs, ys) = unappend @a ls
                               g' = gmap stick split stick split (v &&& ind)
                               gs = omap stick split stick split (play v xs &&&& play ind ys)
                            in evaluate g' ls b)
