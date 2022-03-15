{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}

module Engine.OpenGames
 ( OpenGame(..)
 , lift
 , reindex
 , (>>>)
 , (&&&)
 , (+++)
 ) where


import Engine.OpticClass
import Engine.TLL
import Engine.Diagnostics
import Unsafe.Coerce

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

(>>>) :: (Optic o, Context c o, Unappend a)
      => OpenGame o c a b x s y r -> OpenGame o c a' b' y r z q
      -> OpenGame o c (a +:+ a') (b +:+ b') x s z q
(>>>) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a >>>> play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (cmap identity (play h a') c)
                                                  +:+ evaluate h a' (cmap (play g a) identity c)
}

(&&&) :: (Optic o, Context c o, Unappend a, Show x, Show x')
      => OpenGame o c a b x s y r -> OpenGame o c a' b' x' s' y' r'
      -> OpenGame o c (a +:+ a') (b +:+ b') (x, x') (s, s') (y, y') (r, r')
(&&&) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a &&&& play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (play h a' \\ c)
                                                  +:+ evaluate h a' (play g a // c)
}

--- This works because we assume that a1 and a2 have the same lengths as b1 and b2 respectively.
-- If they don't anything could break because of unsafecoerce.
-- This could be fixed if we knew the length of b1 and b2
-- If the type signature was honest, it would say
-- `MapL NothingL b1 (FctMap Maybe b1), MapL NothingL b2 (FctMap Maybe b2))`
(+++) :: (Optic o, ContextAdd c, Unappend a1, MapL MaybeL b1 (FctMap Maybe b1), MapL MaybeL b2 (FctMap Maybe b2)
         , MapL NothingL a1 (FctMap Maybe a1), MapL NothingL a2 (FctMap Maybe a2))
      => OpenGame o c a1 b1 x1 s y1 r
      -> OpenGame o c a2 b2 x2 s y2 r
      -> OpenGame
          o
          c
          (a1 +:+ a2)
          ((FctMap Maybe b1) +:+ (FctMap Maybe b2))
          (Either x1 x2)
          s
          (Either y1 y2)
          r
(+++) g h  = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a ++++ play h a',
  evaluate =
   \as c ->
     case unappend as of
          (a, a') ->
              let e1 = case prl c of {Nothing -> unsafeCoerce (generateNothingList a)
                                    ; Just c1 -> generateMaybeList (evaluate g a c1)}
                  e2 = case prr c of {Nothing -> unsafeCoerce (generateNothingList a')
                                    ; Just c2 -> generateMaybeList (evaluate h a' c2)}
               in e1 +:+ e2}

