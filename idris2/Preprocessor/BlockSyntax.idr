module Preprocessor.BlockSyntax

import Control.Comonad
import Generics.Derive
import public Data.List1

%language ElabReflection

-- The user interacts with the preprocessor by creating instances of the datatypes in this file
-- and then calling functions from Compiler on it

-- The only reason there is no concrete syntax is that I have no idea how to write a parser
-- Somebody can probably fix that in half an hour
-- My idea for the concrete syntax of a line is
-- cvo, ..., cvo' | cno, ..., cno' <- matrix -< cvi, ..., cvi' | cni, ..., cvi'

-- covariant input = X, covariant output = Y, contravariant input = R, contravariant output = S

-- There is an important duality that the types can't express: half of these are lists of Haskell variables
-- (they could probably be patterns) that create new bindings, and half of them are lists of Haskell expressions
-- Line outputs and block inputs are variables/patterns, line inputs and block outputs are expressions

-- Variables/patterns: covariantOutput, contravariantOutput, blockCovariantInput, blockContravariantInput
-- Expressions:        covariantInput, contravariantInput, blockCovariantOutput, blockContravariantOutput

-- I decided to keep the record field names verbose, and I expect the user to specify lines in constructor syntax
-- rather than record syntax

public export
record Line (p, e : Type) where
  constructor MkLine 
  covariantInputs      : List e
  contravariantOutputs : List p
  matrix               : e
  covariantOutputs     : List p
  contravariantInputs  : List e

%runElab derive "Line" [Generic, Meta, Eq, Show]

pureLine : a -> Line p a
pureLine v = MkLine [] [] v [] []

export
Functor (Line p) where
  map f (MkLine es cos m co ces) = MkLine (map f es) cos (f m) co (map f ces)

export
implementation Applicative (Line p) where
  pure = pureLine
  (MkLine _ _ f _ _) <*> (MkLine covIn conOut m covOut conIn) =
    MkLine (map f covIn) conOut (f m) covOut (map f conIn)

export
implementation Comonad (Line p) where
  extract (MkLine _ _ e _ _) = e
  extend f v = pure (f v)

export
implementation Bifunctor Line where
  mapFst f (MkLine covi cono m covo coni) =
    MkLine covi (map f cono) m (map f covo) coni
  mapSnd = map

export
implementation Foldable (Line p) where
  foldr f init (MkLine _ _ arg _ _)  = f arg init

export
implementation Traversable (Line p) where
  traverse f (MkLine covIn conOut m covOut conIn) =
    pure MkLine <*> traverse f covIn
                <*> pure conOut
                <*> f m
                <*> pure covOut
                <*> traverse f conIn

public export
record Block (p, e : Type) where
  constructor MkBlock 
  blockCovariantInputs : List p 
  blockContravariantOutputs : List e
  blockLines : List1 (Line p e)
  blockCovariantOutputs : List e
  blockContravariantInputs : List p

%runElab derive "Block" [Generic, Meta, Eq, Show]

export
Functor (Block p) where
  map f (MkBlock covIn conOut lines covOut conIn) = MkBlock covIn (map f conOut) (map (map f) lines) (map f covOut) conIn

export
implementation Applicative (Block p) where

  pure v = MkBlock [] [] (pure (pure v)) [] []

  (MkBlock _ _ f _ _) <*> (MkBlock covIn conOut m covOut conIn) =
    let v := map (<*>) f 
        mapLines : List (Line p (a -> b)) -> List a -> List b
        mapLines f as = map extract f <*> as
      in MkBlock covIn
            (mapLines (forget f) conOut)
            (map (<*>) f <*> m)
            (mapLines (forget f) covOut)
            conIn

export
implementation Foldable (Block p) where
  foldr f init (MkBlock _ _ arg _ _)  =
    foldr (\l, b => foldr f b l) init arg

export
implementation Traversable (Block p) where
  traverse f (MkBlock covi cono l covo coni) =
    pure MkBlock <*> pure covi
                 <*> traverse f cono
                 <*> traverse (traverse f) l
                 <*> traverse f covo
                 <*> pure coni

export
implementation Bifunctor Block where
  mapFst f (MkBlock covi cono l covo coni) =
    MkBlock (map f covi) cono (map (mapFst f) l) covo (map f coni)
  mapSnd = map
