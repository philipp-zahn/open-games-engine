||| The AST that is executed after open games have been compiled
module Preprocessor.RuntimeAST

import Data.List

||| Variables are just lists of patterns
public export
record Variables  p where
  constructor MkVariables
  vars : List p

export
Functor Variables where
  map f = MkVariables . map f . vars

||| Expressions are list of expressions
public export
record Expressions e where
  constructor MkExpressions
  exps : List e

export
Functor Expressions where
  map f = MkExpressions . map f . exps

tuple : List String -> String
tuple [x] = x
tuple xs = "(" ++ fastPack (intercalate (unpack ", ") (map unpack xs)) ++ ")"

export
Show e => Show (Variables e) where show = show . vars
export
Show e => Show (Expressions e) where show = show . exps


-- newtype AtomExpression = AtomExpression String
--
-- implementation Show AtomExpression where
--   show (AtomExpression e) = concat ["(", e, ")"]

-- Function expressions are Haskell expressions used as inputs to fromLens (from the class OG)
public export
data FunctionExpression p e = Identity                                 -- \x -> x
                            | Lambda (Variables p) (Expressions e)     -- \(x1, ..., xm) -> (e1, ..., en)
                            | CopyLambda (Variables p) (Expressions e) -- \(x1, ..., xm) -> ((x1, ..., xm), (e1, ..., en))
                            | Multiplex (Variables p) (Variables p)
                            -- \((x1, ..., xm), (y1, ..., yn)) -> (x1, ..., xm, y1, ..., yn)
                            | Curry (FunctionExpression p e)           -- curry f

export
Functor (FunctionExpression p) where
  map f Identity         = Identity
  map f (Lambda x y)     = Lambda x (map f y)
  map f (CopyLambda x y) = CopyLambda x (map f y)
  map f (Multiplex x y)  = Multiplex x y
  map f (Curry x)        = Curry (map f x)

export
implementation Bifunctor FunctionExpression where
  mapFst f Identity = Identity
  mapFst f (Lambda v e) = Lambda (map f v) e
  mapFst f (CopyLambda v e) = CopyLambda (map f v) e
  mapFst f (Multiplex v1 v2) = Multiplex (map f v1) (map f v2)
  mapFst f (Curry fe) = Curry (mapFst f fe)
  mapSnd = map

export
flattenVariables : List (Variables p) -> Variables p
flattenVariables = MkVariables . concat . map vars

export
Show a => Show b => Show (FunctionExpression a b) where
  show Identity         = "\\x -> x"
  show (Lambda x e)     = concat ["\\", show x, " -> ", show e]
  show (CopyLambda x e) = concat ["\\", show x, " -> (", show x, ", ", show e, ")"]
  show (Multiplex x y)  = concat ["\\(", show x, ", ", show y, ") -> ", show (flattenVariables [x, y])]
  show (Curry f)        = concat ["curry (", show f, ")"]

-- The main abstract datatype targeted by the compiler
-- p stands for "patterns", e for "expressions"
public export
data FreeOpenGame p e = Atom e
                      | Lens (FunctionExpression p e) (FunctionExpression p e)
                      | Function (FunctionExpression p e) (FunctionExpression p e)
                      | Counit
                      | Sequential (FreeOpenGame p e) (FreeOpenGame p e)
                      | Simultaneous (FreeOpenGame p e) (FreeOpenGame p e)

export
Functor (FreeOpenGame p) where
  map f (Atom x) = Atom (f x)
  map f (Lens x y) = Lens (map f x) (map f y)
  map f (Function x y) = Function (map f x) (map f y)
  map f Counit = Counit
  map f (Sequential x y) = Sequential (map f x) (map f y)
  map f (Simultaneous x y) = Simultaneous (map f x) (map f y)

export
implementation Bifunctor FreeOpenGame where
  mapFst f (Atom e) = Atom e
  mapFst f (Lens f1 f2) = Lens (mapFst f f1) (mapFst f f2)
  mapFst f (Function fn arg) = Function (mapFst f fn) (mapFst f arg)
  mapFst f Counit = Counit
  mapFst f (Sequential f1 f2) = Sequential (mapFst f f1) (mapFst f f2)
  mapFst f (Simultaneous f1 f2) = Simultaneous (mapFst f f1) (mapFst f f2)
  mapSnd = map

export
Show a => Show b => Show (FreeOpenGame a b)  where
  show (Atom e)           = concat ["(",  show e, ")"]
  show (Lens v u)         = concat ["fromLens (", show v, ") (", show u, ")"]
  show (Function f g)     = concat ["fromFunctions (", show f, ") (", show g, ")"]
  show Counit             = "counit"
  show (Sequential g h)   = concat ["(", show g, ") >>> (", show h, ")"]
  show (Simultaneous g h) = concat ["(", show g, ") &&& (", show h, ")"]

{-
-}
