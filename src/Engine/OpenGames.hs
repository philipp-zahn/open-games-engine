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
 , population
 , fromFunctions
 , (>>>)
 , (&&&)
 ) where


import Engine.OpticClass
import Engine.TLL
import Engine.Vec as Vec
import Engine.Nat
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

pick : [*] -> [*] -> [*]

-- TODO: Check if this works
(+++) :: forall f x1 x2 c o a a' b b' s y1 y2 r.
         (Show x1, Show x2, Optic o, Context c o, ContextAdd c, Unappend a, Unappend a')
      => OpenGame o c a b x1 s y1 r -> OpenGame o c a' b' x2 s y2 r
      -> OpenGame o c (a +:+ a') (b +:+ b') (Either x1 x2) s (Either y1 y2) r
(+++) g1 g2 = OpenGame
  (\ls -> case unappend @a @a' ls of (l1, l2) -> let p1 = play g1 l1
                                                     p2 = play g2 l2
                                                  in p1 ++++ p2)
  (\ls body ->
    case unappend @a @a' ls of
      (l1, l2) -> either (evaluate (_ g1) l1) undefined (match body))-- either (evaluate g1 l1) (evaluate g2 l2) (match body))

-- (+++) :: forall x1 x2 c o a a' b s y1 y2 r.
--          (Show x1, Show x2, Optic o, Context c o, ContextAdd c, Unappend a, Unappend a')
--       => OpenGame o c a b x1 s y1 r -> OpenGame o c a' b x2 s y2 r
--       -> OpenGame o c (a +:+ a') b (Either x1 x2) s (Either y1 y2) r
-- (+++) g1 g2 = OpenGame
--   (\ls -> case unappend @a @a' ls of (l1, l2) -> let p1 = play g1 l1
--                                                      p2 = play g2 l2
--                                                   in p1 ++++ p2)
--   (\ls body ->
--     case unappend @a @a' ls of
--       (l1, l2) -> either (evaluate g1 l1) (evaluate g2 l2) (match body))

(&&&) :: (Optic o, Context c o, Unappend a, Unappend b, Show x, Show x')
      => OpenGame o c a b x s y r -> OpenGame o c a' b' x' s' y' r'
      -> OpenGame o c (a +:+ a') (b +:+ b') (x, x') (s, s') (y, y') (r, r')
(&&&) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a &&&& play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (play h a' \\ c)
                                                 +:+ evaluate h a' (play g a // c)
}

fromFunctions :: forall o c a b x s y r.
  Optic o => Context c o => (x -> y) -> (r -> s) -> OpenGame o c '[] '[] x s y r
fromFunctions f g = lift (lens f (const g))

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

-- Split a vector into its head and tail, opposite of `cons`
uncons :: Vec (S n) a -> (a, Vec n a)
uncons (x :> xs) = (x, xs)

-- Stick a value and a vector together, opposite of `uncons`
cons :: (a, Vec n a) -> Vec (S n) a
cons (x, xs) = x :> xs

-- Duplicates a player `n` times where `n` must be >= 1
population :: forall o c a b x s y r n.
  (Optic o, Context c o, Unappend a, Unappend b, Show x) =>
  Natural n ->
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
                                        omap cons uncons cons uncons (p1 &&&& p2))
               (\ls b ->
                 case repeatSuccProof of
                   Refl -> let (xs, ys) = unappend @a ls
                               g' = gmap cons uncons cons uncons (v &&& ind)
                               gs = omap cons uncons cons uncons (play v xs &&&& play ind ys)
                            in evaluate g' ls b)
