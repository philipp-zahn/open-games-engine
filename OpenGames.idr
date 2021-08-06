module OpenGames

import Data.List

infixr 8 >>>>
infixl 7 &&&&
infixl 6 ++++

%hide Prelude.either

either : (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left a) = f a
either f g (Right b) = g b

interface Optic (0 o : Type -> Type -> Type -> Type -> Type) where
  lens : (s -> a) -> (s -> b -> t) -> o s t a b
  (>>>>) : o s t a b -> o a b p q -> o s t p q
  (&&&&) : o s1 t1 a1 b1 -> o s2 t2 a2 b2 -> o (s1, s2) (t1, t2) (a1, a2) (b1, b2)
  (++++) : o s1 t a1 b -> o s2 t a2 b -> o (Either s1 s2) t (Either a1 a2) b

identity : (Optic o) => o s t s t
identity = lens id (flip const)

interface (Optic o) => Context (0 c, o : Type -> Type -> Type -> Type -> Type) where
  cmap : o s1 t1 s2 t2 -> o a1 b1 a2 b2 -> c s1 t1 a2 b2 -> c s2 t2 a1 b1
  (//) : o s1 t1 a1 b1 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s2 t2 a2 b2
  (\\) : o s2 t2 a2 b2 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s1 t1 a1 b1

interface ContextAdd (0 c : Type -> Type -> Type -> Type -> Type) where
  match : c (Either x1 x2) s (Either y1 y2) r -> Either (c x1 s y1 r) (c x2 s y2 r)
  both : c (x, x') (s, s') (y, y') (r, r') -> (c x s y r, c x' s' y' r')

data TypeList : List Type -> Type where
  Nil : TypeList []
  (::) : (ty : Type) -> TypeList ts -> TypeList (ty :: ts)

FromList : (ls : List Type) -> TypeList ls
FromList [] = []
FromList (x :: xs) = x :: FromList xs

record OpenGame (o, c : Type -> Type -> Type -> Type -> Type)
                (a : List Type)
                (x, s, y, r : Type)
                (f : c x s y r -> List Type)
                where
  constructor MkGame
  play : TypeList a -> o x s y r
  evaluate : TypeList a -> (v : c x s y r) -> TypeList (f v)

(++) : TypeList xs -> TypeList ys -> TypeList (xs ++ ys)
(++) [] y = y
(++) (ty :: x) y = ty :: (x ++ y)

split : {xs : _} -> TypeList (xs ++ ys) -> (TypeList xs, TypeList ys)
split x {xs = []} = ([], x)
split (y :: ts) {xs = (y :: xs)} =
  let (xs', ys') = OpenGames.split ts in (y :: xs', ys')

left : {xs : _} -> TypeList (xs ++ ys) -> TypeList xs
left = fst . split

right : {xs : _} -> TypeList (xs ++ ys) -> TypeList ys
right = snd . split

choice : (select : Bool) -> (b : TypeList ks) -> (b' : TypeList ks')
      -> TypeList (if select then ks else ks')
choice True b b' = b
choice False b b' = b'

sequenceTy : Optic o => Context c o 
         => o x s y r -> o y r z q 
	 -> (c x s y r -> List Type) 
	 -> (c y r z q -> List Type) 
	 -> (c x s z q -> List Type)
sequenceTy o1 o2 f g w = f (cmap {o} identity o2 w)
                     ++ g (cmap {o} o1 identity w)

TensorTy : {0 c : Type -> Type -> Type -> Type -> Type} ->
           (c x s y r -> List Type) ->
	   (c x' s' y' r' -> List Type) ->
           (c x s y r, c x' s' y' r') ->
	   List Type
TensorTy fl fr (l, r) = fl l ++ fr r

-- Sequence operator
(>>>) : {a, a' : List Type } -> (Optic o, Context c o)
      => (g1 : OpenGame o c a x s y r b) -> (g2 : OpenGame o c a' y r z q b')
      -> OpenGame o c (a ++ a') x s z q
                      (sequenceTy {c} {o} (g1.play (FromList a)) (g2.play (FromList a')) b b')
(>>>) g1 g2 =
  MkGame
    (\tl => case split tl of (left, right) => g1.play left >>>> g2.play right)
    (\tl, body => case split tl of (left, right) => let v1 = g1.evaluate left (cmap {c} {o} identity (g2.play (FromList a')) body)
                                                        v2 = g2.evaluate right (cmap {c} {o} (g1.play (FromList a)) identity body)
                                                     in v1 ++ v2)

-- Choice operator
(+++) : {a : _} -> Optic o => Context c o => ContextAdd c
     => (a, a' : List Type)
     -> (g1 : OpenGame o c a x1 s y1 r b) -> (g2 : OpenGame o c a' x2 s y2 r b')
     -> OpenGame o c
                 (a ++ a')
                 (Either x1 x2) s (Either y1 y2) r
                 (either b b' . (OpenGames.match {c} {y1} {y2}))
(+++) a a' g h = MkGame
  (\tl => case split tl of (left, right) => g.play left ++++ h.play right)
  fn
  where
    fn : TypeList (a ++ a') -> (v : c (Either x1 x2) s (Either y1 y2) r) -> TypeList (either b b' (match {y1} {y2} v))
    fn args ctx with (match ctx)
      fn args ctx | (Left x) = g.evaluate (left args) x
      fn args ctx | (Right x) = h.evaluate (right args) x

(&&&) : (Optic o, Context c o, ContextAdd c)
     => {a, a' : List Type}
     -> {b : c x s y r -> List Type}
     -> {b' : c x' s' y' r' -> List Type}
     -> (g1 : OpenGame o c a x s y r b) 
     -> (g2 : OpenGame o c a' x' s' y' r' b')
     -> OpenGame o c (a ++ a') (x, x') (s, s') (y, y') (r, r') 
                     (TensorTy {c} b b' . (OpenGames.both {c}))
(&&&) g1 g2 = MkGame
    (\tl => let (l, r) = split tl in g1.play l &&&& g2.play r)
    eval
    where
      eval : TypeList (a ++ a') -> (v : c (x, x') (s, s') (y, y') (r, r'))
          -> TypeList (TensorTy {c} b b' (both v))
      eval ty v with (both v)
        eval ty v | (left, right) = 
	  let (la, la') = split ty in g1.evaluate la left ++ g2.evaluate la' right

{-
-}
