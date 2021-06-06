{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
-- {-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs                 #-}


-- Parts of this file were written by Sjoerd Visscher

module Engine.TLL
  ( List(..)
  , Apply(..)
  , Unappend(..)
  , MapL(..)
  , FoldrL(..)
  , ConstMap(..)
  , SequenceList(..)
  , Natural(..)
  , IndexList(..)
  , ToList(..)
  , type (+:+)
  , (+:+)
  , Repeat(..)
  , CatRepeat(..)
  , repeat1Proof
  , repeatSuccProof
  ) where

import Control.Applicative
import Data.Kind
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce (unsafeCoerce)
import Engine.Nat
import Engine.Vec
import Prelude hiding (replicate)

infixr 6 ::-
-- Type-level lists: A list of types
data List (ts :: [*]) where
  Nil :: List '[]
  (::-) :: t -> List ts -> List (t ': ts)

data SList (ls :: List ts) where
  SNil :: SList 'Nil
  SCons :: SList (t ::- ts)

instance Show (List '[]) where
    show Nil = "Nil"

instance (Show (List as), Show a)
    => Show (List (a ': as)) where
    show (a ::- rest) =
        show a ++ " ::- " ++ show rest

-- Concatenation of two lists of types
type family (+:+) (as :: [*]) (bs :: [*]) :: [*] where
  '[] +:+ bs = bs
  (a ': as) +:+ bs = a ': (as +:+ bs)

-- Append two `List`s together while keeping track of the types they carry
(+:+) :: List as -> List bs -> List (as +:+ bs)
(+:+) Nil bs = bs
(+:+) (a ::- as) bs = a ::- as +:+ bs

-- Class that advertises that a list is composed from the concatenation
-- of two other lists, `as` is the first of the two lists
class Unappend as where
  unappend :: List (as +:+ bs) -> (List as, List bs)

-- if the first of the two lists is `[]` then the second one is just `bs`
instance Unappend '[] where
  unappend bs = (Nil, bs)

-- If the first list is not empty, we need to unappend is tail in order to
-- reach `bs` and then rebuild `as` from the recursive calls
instance Unappend as => Unappend (a ': as) where
  unappend (a ::- abs) = case unappend abs of (as, bs) -> (a ::- as, bs)

-- append the empty list does nothing
appendNilNeutral :: ls +:+ '[] :~: ls
appendNilNeutral = unsafeCoerce Refl -- Two reasons for this:
                                     -- 1. we already know it works thanks to Idris
                                     -- 2. We don't want the runtime cost of
                                     --    iterating through `ls` to prove this

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

-- Indexing on the list

class IndexList (n :: Nat) (xs :: [Type]) (i :: Type) | n xs -> i where
   fromIndex :: Natural n -> List xs -> i

instance IndexList Z (x ': xs) x where
   fromIndex Zero (x ::- _) = x

instance IndexList n xs a => IndexList (S n) (x ': xs) a where
   fromIndex (Succ n) (_ ::- xs) = fromIndex n xs

class ToList f where
  toList :: f a -> [a]

instance ToList (Vec n) where
  toList Empty = []
  toList (x :> xs) = x : toList xs

instance (Show a) => Show (Vec n a) where
  show = show . toList

type family Repeat (n :: Nat) (e :: t) :: Vec n t where
  Repeat Z e = 'Empty
  Repeat (S n) e = e :> Repeat n e

type family RepeatLs (n :: Nat) (e :: [*]) :: [[*]] where
  RepeatLs Z ls = '[]

-- Repeats a TLL `n` times, concatenating each instance to the next
type family CatRepeat (n :: Nat) (ls :: [*]) :: [*]  where
  CatRepeat Z ls = '[]
  CatRepeat (S n) ls = ls +:+ CatRepeat n ls

-- repeating a list once is the same a getting back the original vector
repeat1Proof :: forall a. CatRepeat (S Z) a :~: a
repeat1Proof = appendNilNeutral

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

-- A proofs about the fact that a single step of repeating a list is the same
-- as concatenating the list in the front and the using `CatRepeat` but one
-- time less
repeatSuccProof :: forall (n :: Nat) (ls :: [*]) . CatRepeat (S n) ls :~: (ls +:+ CatRepeat n ls)
repeatSuccProof = Refl
