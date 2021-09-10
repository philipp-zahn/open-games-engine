{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module Test where

import Data.Kind (Type)
import Data.Proxy

-- Part 0
type family StrOrInt (b :: Bool) :: Type where
  StrOrInt True = String
  StrOrInt False = Int

data SBool :: Bool -> Type where
  SFalse :: SBool False
  STrue :: SBool True

getVal :: SBool b -> StrOrInt b
getVal STrue = "Hello"
getVal SFalse = 30

-- Part 1
data Nat = Z | S Nat

toInt :: Nat -> Int
toInt Z = 0
toInt (S n) = 1 + toInt n

instance Show Nat where
  show = show . toInt

data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data Vec :: Nat -> Type -> Type where
  Nil :: Vec Z t
  Cons :: t -> Vec n t -> Vec (S n) t

data Index :: Nat -> Type where
  Zero :: Index (S n)
  Succ :: Index n -> Index (S n)

toNat :: Index n -> Nat
toNat Zero = Z
toNat (Succ n) = S (toNat n)

instance Show (Index n) where
  show = show . toNat

indexVec :: Index n -> Vec n a -> a
indexVec Zero (Cons x xs) = x
indexVec (Succ n) (Cons x xs) = indexVec n xs

findVec :: (a -> Bool) -> Vec n a -> Maybe (Index n)
findVec check Nil = Nothing
findVec check (Cons x xs) = if check x then Just Zero
                                       else case findVec check xs of
                                                 Nothing -> Nothing
                                                 Just idx -> Just (Succ idx)

findSecond = findVec (== 3) (Cons 1 (Cons 2 (Cons 3 Nil)))

-- Part 2

data HVec :: forall n. Vec n Type -> Type where
  HNil :: HVec Nil
  HCons :: forall t ts. t -> HVec ts -> HVec (Cons t ts)

heterogenous :: HVec (Cons String (Cons Int (Cons Nat Nil)))
heterogenous = HCons "hello" (HCons 3 (HCons (S Z) HNil))

data Elem :: forall n. a -> Vec n a -> Type where
  Here :: Elem t (Cons t ts)
  There :: Elem t ts -> Elem t (Cons s ts)

indexHVec :: Elem t ts -> HVec ts -> t
indexHVec Here (HCons x xs) = x
indexHVec (There idx) (HCons x xs) = indexHVec idx xs


type Predicates :: Vec n Type -> Vec n Type
type family Predicates xs where
  Predicates Nil = Nil
  Predicates (Cons x xs) = Cons (x -> Bool) (Predicates xs)


type family (~>) :: Type -> Type -> Type
infixr 0 ~>
type family (@@) :: (a ~> b) -> (a :: Type) -> (b :: Type)
infixl 1 @@

flipFn :: (a -> b -> c) -> (b -> a -> c)
flipFn fn b a = fn a b

type Flip :: (a ~> b ~> c) -> b -> a -> c
type family Flip fn b a where
  Flip fn b a =  fn @@ a @@ b

-- type instance Elem0 @@ x = Elem1 x
-- type instance (Elem1 x) @@ xs = Elem x xs

type KindOf (a :: k ) = ('KProxy :: KProxy k )

-- data Elem1 x xs where
--   -- Elem1Inf :: KindOf (Elem1 x @@ xs) ~ KindOf (Elem x xs) => Elem1 x xs
--   Elem1Inf :: Elem1 x xs

-- type Elem0 :: a ~> Vec n a ~> Type
-- data Elem0 x where
--   Elem0Inf :: KindOf (Elem0 @@ x) ~ KindOf (Elem1 x) => Elem0 x
-- Elem0Inf :: Elem0 x
type Map :: (a ~> b) -> Vec n a -> Vec n b
type family Map f xs where
  Map f Nil = Nil
  Map f (Cons x xs) = Cons (f @@ x) (Map f xs)

data MapSym1 x f where
  MapSym1KindInference :: KindOf ((MapSym1 x) @@ arg ) ~ KindOf (Map x arg ) => MapSym1 x f

data MapSym0 f where
  MapSym0KindInference :: KindOf (MapSym0 @@ arg )~ KindOf (MapSym1 arg ) => MapSym0 f

-- this is (Σ x : Type. y)
data SigmaType :: (Type -> Type) -> Type where


-- findHVec :: forall (n :: Nat) (ts :: Vec n Type). 
--             HVec (Predicates ts) -> HVec ts  -> Maybe (SigmaType (FlipElem ts))
-- findHVec HNil HNil = Nothing
-- findHVec (HCons p ps) (HCons x xs) = 
--   if p x then Just ()
--          else findHVec ps xs
-- 
-- 
-- 
-- -- Part 3
-- 
-- type Pair :: Type -> Type -> Type
-- data Pair a b = MkPair a b
-- 
-- data Unit = MkUnit
-- 
-- type family SemigroupF :: (a :: Type) -> (a -> a -> a) -> Type
-- 
-- instance Semigroup Type where
--   (<>) = Pair
-- 
-- instance Monoid Type where
--   mempty = undefined
