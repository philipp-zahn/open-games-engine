{-# LANGUAGE DataKinds
           , DefaultSignatures
           , EmptyCase
           , ExistentialQuantification
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , InstanceSigs
           , KindSignatures
           , NoCUSKs
           , NoStarIsType
           , PolyKinds
           , RankNTypes
           , ScopedTypeVariables
           , StandaloneDeriving
           , StandaloneKindSignatures
           , TemplateHaskell
           , TypeApplications
           , TypeFamilies
           , TypeOperators
           , UndecidableInstances #-}

module Engine.OpenGames where
--  ( OpenGame(..)
--  , lift
--  , reindex
--  , population
--  , fromFunctions
--  , play
--  , evaluate
--  , (>>>)
--  , (&&&)
--  ) where


import Engine.OpticClass as OC
import qualified Engine.TLL as TLL
import Engine.Vec as Vec
import Engine.Nat
import Data.Type.Equality ((:~:)(..))
import Data.Kind (Type)
import Data.Singletons
import Data.Singletons.TH as STH
import Prelude.Singletons

import Unsafe.Coerce

data OpenGame (o :: Type -> Type -> Type -> Type -> Type)
              (c :: Type -> Type -> Type -> Type -> Type)
              (a :: [Type])
              (x :: Type) (s :: Type)
              (y :: Type) (r :: Type)
              (b :: c x s y r ~> [Type])
    where
  OpenGame :: { play :: (TLL.List a -> o x s y r)
              , eval :: (forall ctx. TLL.List a -> Sing (ctx :: c x s y r) -> TLL.List (b @@ ctx))
              } -> OpenGame o c a x s y r b

(+++) :: forall x1
                x2
                (c :: Type -> Type -> Type -> Type -> Type)
                (o :: Type -> Type -> Type -> Type -> Type)
                (a :: [Type])
                (a' :: [Type])
                s
                y1
                r
                (b :: c x1 s y1 r ~> [Type])
                y2
                (b' :: c x2 s y2 r ~> [Type]).
         (Show x1, Show x2, Optic o, Context c o, ContextAdd c, TLL.Unappend a, TLL.Unappend a', SContextAdd c, SingKind (c (Choice x1 x2) s (Choice y1 y2) r))
      => OpenGame o c a x1 s y1 r b -> OpenGame o c a' x2 s y2 r b'
      -> OpenGame o c (a TLL.+:+ a') (Choice x1 x2) s (Choice y1 y2) r (ChoiceTySym2 @c @x1 @s @y1 @r @x2 @y2 b b')
(+++) g1 g2 =
  OpenGame
    (\ls -> case TLL.unappend @a @a' ls of (l1, l2) -> let p1 = play g1 l1
                                                           p2 = play g2 l2
                                                        in p1 ++++ p2)
    (\ls body ->
      case TLL.unappend @a @a' ls of
        (l1, l2) -> case sMatch body of
                         SChoice1 x -> eval g1 l1 x
                         SChoice2 x -> eval g2 l2 x)

$(promote [d|
  sequenceTy :: (Optic o, Context c o)
           => o x s y r -> o y r z q
           -> (c x s y r -> [Type])
           -> (c y r z q -> [Type])
           -> (c x s z q -> [Type])
  sequenceTy o1 o2 f g w = f (cmap identity o2 w)
                        ++ g (cmap o1 identity w)|])

-- (>>>) :: (Optic o, Context c o, TLL.Unappend a, TLL.Unappend b)
--       => OpenGame o c a x s y r b -> OpenGame o c a' y r z q b'
--       -> OpenGame o c (a TLL.+:+ a') x s z q (b TLL.+:+ b')
-- (>>>) g h = OpenGame
--   (\as -> case unappend as of (a, a') -> play g a >>>> play h a')
--   (\as c -> case unappend as of (a, a') -> evaluate g a (cmap identity (play h a') c)
--                                    TLL.+:+ evaluate h a' (cmap (play g a) identity c))

-- Idris version
--
-- SequenceTy : Optic o => Context c o
--          => o x s y r -> o y r z q
-- 	 -> (c x s y r -> List Type)
-- 	 -> (c y r z q -> List Type)
-- 	 -> (c x s z q -> List Type)
-- SequenceTy o1 o2 f g w = f (cmap {o} identity o2 w)
--                       ++ g (cmap {o} o1 identity w)
-- (>>>) : {a, a' : List Type } -> (Optic o, Context c o)
--       => (g1 : OpenGame o c a x s y r b) -> (g2 : OpenGame o c a' y r z q b')
--       -> OpenGame o c (a ++ a') x s z q
--                       (SequenceTy {c} {o} (g1.play (FromList a)) (g2.play (FromList a')) b b')
-- (>>>) g1 g2 =
--   MkGame
--     (\tl => case split tl of (left, right) => g1.play left >>>> g2.play right)
--     (\tl, body => case split tl of (left, right) => let v1 = g1.evaluate left (cmap {c} {o} identity (g2.play (FromList a')) body)
--                                                         v2 = g2.evaluate right (cmap {c} {o} (g1.play (FromList a)) identity body)
--                                                      in v1 ++ v2)
-- $(promote [d|
--   constTy :: a -> (b -> a)
--   constTy v _ = v|])
--
--
-- lift :: o x s y r -> OpenGame o c '[] x s y r ConstTy
-- lift o = OpenGame
--   (\TLL.Nil -> o)
--   (\TLL.Nil _ -> TLL.Nil)
--
-- reindex :: (TLL.List a -> TLL.List a') -> (TLL.List a -> TLL.List b' -> TLL.List b)
--         -> OpenGame o c a' x s y r b' -> OpenGame o c a x s y r b
-- reindex v u g = OpenGame
--   {- play: -} (\a -> play g (v a))
--   {- evaluate: -} (\a c -> u a (evaluate g (v a) c))
--
-- (&&&) :: (Optic o, Context c o, TLL.Unappend a, TLL.Unappend b, Show x, Show x')
--       => OpenGame o c a x s y r b -> OpenGame o c a' x' s' y' r' b'
--       -> OpenGame o c (a TLL.+:+ a') (x, x') (s, s') (y, y') (r, r') (b TLL.+:+ b')
-- (&&&) g h = OpenGame
--   {- play: -} (\as -> case unappend as of (a, a') -> play g a &&&& play h a')
--   {- evaluate: -} (\as c -> case unappend as of (a, a') -> evaluate g a (play h a' \\ c)
--                                                    TLL.+:+ evaluate h a' (play g a // c))
--
-- fromFunctions :: forall o c a x s y r b .
--   Optic o => Context c o => (x -> y) -> (r -> s) -> OpenGame o c '[] x s y r '[]
-- fromFunctions f g = lift (lens f (const g))
--
-- omap :: Optic o =>
--         (s -> s') ->
--         (x' -> x) ->
--         (y -> y') ->
--         (r' -> r) ->
--         o x s y r -> o x' s' y' r'
-- omap g g1 g2 g3 optic = lens g1 (const g) >>>> (optic >>>> lens g2 (const g3) )
--
-- gmap :: forall c o a b s s' x x' y y' r r'. (Optic o, Context c o) =>
--         (s -> s') ->
--         (x' -> x) ->
--         (y -> y') ->
--         (r' -> r) ->
--         OpenGame o c a x s y r b ->
--         OpenGame o c a x' s' y' r' b
-- gmap f1 f2 f3 f4 (OpenGame p e) =
--     OpenGame (\t -> omap f1 f2 f3 f4 (p t))
--              (\t b -> e t (cmap @c @o (lens f2 (const f1)) (lens f3 (const f4)) b))
--
--
-- pop1 :: forall o c a b x s y r. (Optic o, Context c o) => OpenGame o c a x s y r b ->
--   OpenGame o c (TLL.CatRepeat (S Z) a)
--                (Vec (S Z) x) (Vec (S Z) s) (Vec (S Z) y) (Vec (S Z) r)
--                (TLL.CatRepeat (S Z) b)
-- pop1 game =
--   let v = gmap mkVec (vecHead @Z) mkVec (vecHead @Z) game
--    in case repeat1Proof @a of
--         Refl -> case repeat1Proof @b of Refl -> v
--
-- -- Split a vector into its head and tail, opposite of `cons`
-- uncons :: Vec (S n) a -> (a, Vec n a)
-- uncons (x :> xs) = (x, xs)
--
-- -- Stick a value and a vector together, opposite of `uncons`
-- cons :: (a, Vec n a) -> Vec (S n) a
-- cons (x, xs) = x :> xs
--
-- -- combines `n` players into a single game
-- population :: forall o c a b x s y r n.
--   (Optic o, Context c o, TLL.Unappend a, TLL.Unappend b, Show x) =>
--   Natural n ->
--   (Vec (S n) (OpenGame o c a x s y r b)) ->
--   OpenGame o c (TLL.CatRepeat (S n) a)
--                (Vec (S n) x) (Vec (S n) s) (Vec (S n) y) (Vec (S n) r)
--                (TLL.CatRepeat (S n) b)
-- population Zero (v :> Empty) = pop1 v
-- population (Succ n) (v :> v' :> vs) =
--   let ind = population n (v' :> vs) in
--       OpenGame (\ls -> case repeatSuccProof @n @a of
--                             Refl -> let (xs, ys) = unappend @a ls
--                                         p1 = play v xs
--                                         p2 = play ind ys in
--                                         omap cons uncons cons uncons (p1 &&&& p2))
--                (\ls b ->
--                  case repeatSuccProof of
--                    Refl -> let (xs, ys) = unappend @a ls
--                                g' = gmap cons uncons cons uncons (v &&& ind)
--                                gs = omap cons uncons cons uncons (play v xs &&&& play ind ys)
--                             in evaluate g' ls b)
--
