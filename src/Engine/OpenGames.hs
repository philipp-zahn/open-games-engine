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
 ) where


import Engine.OpticClass
import Engine.TLL

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

(>>>) :: (Optic o, Context c o, Unappend a, Unappend b) -- TODO check Unappend b
      => OpenGame o c a b x s y r -> OpenGame o c a' b' y r z q
      -> OpenGame o c (a +:+ a') (b +:+ b') x s z q
(>>>) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a >>>> play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (cmap identity (play h a') c)
                                                  +:+ evaluate h a' (cmap (play g a) identity c)
}

(&&&) :: (Optic o, Context c o, Unappend a, Unappend b, Show x, Show x') -- TODO check Unappend b
      => OpenGame o c a b x s y r -> OpenGame o c a' b' x' s' y' r'
      -> OpenGame o c (a +:+ a') (b +:+ b') (x, x') (s, s') (y, y') (r, r')
(&&&) g h = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a &&&& play h a',
  evaluate = \as c -> case unappend as of (a, a') -> evaluate g a (play h a' \\ c)
                                                  +:+ evaluate h a' (play g a // c)
}

(+++) :: forall o c a a' b b1 bs b' b1' bs' x s y y' r.  ((b ~ (b1 ': bs)), ((b' ~ (b1' ': bs')), Optic o, Context c o, Unappend a, Show x))
      => OpenGame o c a b x s y r -> OpenGame o c a' b' x s y' r
      -> OpenGame o c (a +:+ a') (FctMap Maybe b +:+ FctMap Maybe b') (Either x x) s (Either y y') r
(+++) g h  = OpenGame {
  play = \as -> case unappend as of (a, a') -> play g a ++++ play h a',
  evaluate = 
   \as c ->
     case unappend as of (a, a') -> let e1 = case prl c of {Nothing -> Nothing ::- Nil ; Just c1 ->
                                                            test (evaluate g a c1)}
                                        e2 = undefined-- case prr c of {Nothing -> Nothing ::- Nil ; Just c2 -> mapL Just @_ @(FctMap Maybe b') (Just (evaluate h a' c2))}
                                                 in e1 +:+ e2}

M
--testFunction :: FctMap Maybe xs 
--testFunction hlist = mapL Just hlist

test :: forall x xs' xs. ((xs ~ (x ': xs')), MapL (x -> Maybe x) xs (FctMap Maybe xs) ) => List xs -> List (FctMap Maybe xs) 
test xs = mapL @(x -> Maybe x) @_ @(FctMap Maybe xs) Just xs

elem1 :: Int
elem1 = 1

elemA :: String
elemA = "a"

test2 = test (elem1 ::-  elem1 ::- Nil)
