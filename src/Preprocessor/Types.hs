{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module Preprocessor.Types where

import Data.List (intercalate)
import Data.Bifunctor
import Language.Haskell.TH

newtype Variables   p = Variables {vars :: [p]} deriving (Eq, Functor)
newtype Expressions e = Expressions {exps :: [e]} deriving (Eq, Functor)

tuple :: [String] -> String
tuple [x] = x
tuple xs = "(" ++ intercalate ", " xs ++ ")"

instance Show (Variables String) where show = tuple . vars
instance Show (Expressions String) where show = tuple . exps


-- newtype AtomExpression = AtomExpression String
--
-- instance Show AtomExpression where
--   show (AtomExpression e) = concat ["(", e, ")"]

-- Function expressions are Haskell expressions used as inputs to fromLens (from the class OG)
data FunctionExpression p e = Identity                                 -- \x -> x
                            | Copy                                     -- \x -> (x, x)
                            | Lambda (Variables p) (Expressions e)     -- \(x1, ..., xm) -> (e1, ..., en)
                            | CopyLambda (Variables p) (Expressions e) -- \(x1, ..., xm) -> ((x1, ..., xm), (e1, ..., en))
                            | Multiplex (Variables p) (Variables p)    -- \((x1, ..., xm), (y1, ..., yn)) -> (x1, ..., xm, y1, ..., yn)
                            | Curry (FunctionExpression p e)           -- curry f
                            deriving (Eq, Functor)

instance Bifunctor FunctionExpression where
  first f Identity = Identity
  first f Copy = Copy
  first f (Lambda v e) = Lambda (fmap f v) e
  first f (CopyLambda v e) = CopyLambda (fmap f v) e
  first f (Multiplex v1 v2) = Multiplex (fmap f v1) (fmap f v2)
  first f (Curry fe) = Curry (first f fe)
  second = fmap

flattenVariables :: [Variables p] -> Variables p
flattenVariables = Variables . concat . map vars

instance Show (FunctionExpression String String) where
  show Identity         = "\\x -> x"
  show Copy             = "\\x -> (x, x)"
  show (Lambda x e)     = concat ["\\", show x, " -> ", show e]
  show (CopyLambda x e) = concat ["\\", show x, " -> (", show x, ", ", show e, ")"]
  show (Multiplex x y)  = concat ["\\(", show x, ", ", show y, ") -> ", show (flattenVariables [x, y])]
  show (Curry f)        = concat ["curry (", show f, ")"]

-- The main abstract datatype targeted by the compiler
-- p stands for "patterns", e for "expressions"
data FreeOpenGame p e = Atom e
                      | Lens (FunctionExpression p e) (FunctionExpression p e)
                      | Function (FunctionExpression p e) (FunctionExpression p e)
                      | Counit
                      | Sequential (FreeOpenGame p e) (FreeOpenGame p e)
                      | Simultaneous (FreeOpenGame p e) (FreeOpenGame p e)
                      deriving (Eq, Functor)

instance Bifunctor FreeOpenGame where
  first f (Atom e) = Atom e
  first f (Lens f1 f2) = Lens (first f f1) (first f f2)
  first f (Function fn arg) = Function (first f fn) (first f arg)
  first f Counit = Counit
  first f (Sequential f1 f2) = Sequential (first f f1) (first f f2)
  first f (Simultaneous f1 f2) = Simultaneous (first f f1) (first f f2)
  second = fmap

instance Show (FreeOpenGame String String)  where
  show (Atom e)           = concat ["(",  e, ")"]
  show (Lens v u)         = concat ["fromLens (", show v, ") (", show u, ")"]
  show (Function f g)     = concat ["fromFunctions (", show f, ") (", show g, ")"]
  show Counit             = "counit"
  show (Sequential g h)   = concat ["(", show g, ") >>> (", show h, ")"]
  show (Simultaneous g h) = concat ["(", show g, ") &&& (", show h, ")"]

instance Show (FreeOpenGame String Exp) where
  show game = show $ fmap show game
