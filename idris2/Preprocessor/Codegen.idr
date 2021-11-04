module Preprocessor.Codegen

import Preprocessor.RuntimeAST
import Preprocessor.CompileSyntax

import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Types

||| apply a function to a list of arguments
apply : TTImp -> List TTImp -> TTImp
apply fn [] = fn
apply fn (x :: xs) = apply (IApp EmptyFC fn x) xs

||| Basically a fold
nestedApply : (f : a -> a -> a) -> a -> List a -> a
nestedApply combine f [] = f
nestedApply combine f [x] = x
nestedApply combine f (x :: xs) = combine (combine f x) (nestedApply combine f xs)

tuplize : List TTImp -> TTImp
tuplize = nestedApply (@@) `(MkPair)

naiveAppend : List a -> List a -> List a

inferTy : TTImp
inferTy = Implicit EmptyFC False

-- Convert a pattern into the left hand side of a clause
patClauseLHS : Pat TTImp -> TTImp
patClauseLHS (VarP x) = IVar EmptyFC x
patClauseLHS (LitP x) = x
patClauseLHS (ConP x xs) = apply (IVar EmptyFC (UN (Basic x))) (map patClauseLHS xs)


patLambda : (args : Pat TTImp) -> (body : TTImp) -> TTImp
patLambda (VarP x) body = ILam EmptyFC MW ExplicitArg (Just x) inferTy body
patLambda arg body = ILam EmptyFC MW ExplicitArg (Just (MN "caseArg" 0)) inferTy $
                                ICase EmptyFC (IVar EmptyFC (MN "caseArg" 0)) inferTy
                                    [PatClause EmptyFC (patClauseLHS arg) body ]

PairP : Pat a -> Pat a -> Pat a
PairP p1 p2 = ConP "MkPair" [p1, p2]

returnValue : List TTImp -> TTImp
returnValue [] = `(MkUnit)
returnValue (x :: []) = x
returnValue (x :: xs) = `(MkPair) @@ x @@ returnValue xs

interpretLambda : List (Pat TTImp) -> List TTImp -> TTImp
interpretLambda [] ys =
  ILam EmptyFC MW ExplicitArg Nothing `(Unit) (returnValue ys)
interpretLambda ((VarP x) :: []) ys =
  ILam EmptyFC MW ExplicitArg (Just x) inferTy (returnValue ys)
interpretLambda (pat :: []) ys =
  ILam EmptyFC MW ExplicitArg (Just (MN "lamArg" 0)) inferTy
    (ICase EmptyFC (IVar EmptyFC (MN "lamArg"0)) inferTy
        [PatClause EmptyFC (patClauseLHS pat) (returnValue ys)])
interpretLambda (pat :: (y :: xs)) ys =
  ILam EmptyFC MW ExplicitArg (Just (MN "lamArg" 0)) inferTy
    (ICase EmptyFC (IVar EmptyFC (MN "lamArg"0)) inferTy
        [PatClause EmptyFC (patClauseLHS pat) (interpretLambda (y :: xs) ys)])

interpretFunction : FunctionExpression (Pat TTImp) TTImp -> TTImp
interpretFunction Identity = `(id)
interpretFunction (Curry f) = `(curry) @@ interpretFunction f
interpretFunction (Lambda (MkVariables vars) (MkExpressions exps)) =
  interpretLambda vars exps

interpretFunction (CopyLambda (MkVariables { vars }) (MkExpressions { exps })) =
  interpretLambda vars [tuplize (map patClauseLHS vars), tuplize exps]
interpretFunction (Multiplex (MkVariables { vars }) (MkVariables { vars = vars' })) =
  interpretLambda [nestedApply PairP (ConP "MkUnit" []) vars, nestedApply PairP (ConP "MkUnit" []) vars'] (map patClauseLHS vars ++ map patClauseLHS vars')

interpretOpenGame : FreeOpenGame (Pat TTImp) TTImp -> TTImp
interpretOpenGame (Atom n) = n
interpretOpenGame (Lens f1 f2) = `(fromLens) @@ interpretFunction f1 @@ interpretFunction f2
interpretOpenGame (Function f1 f2) = `(fromFunctions) @@ interpretFunction f1 @@ interpretFunction f2
interpretOpenGame Counit = `(counit)
interpretOpenGame (Sequential g1 g2) = `((>>>)) @@ interpretOpenGame g1 @@ interpretOpenGame g2
interpretOpenGame (Simultaneous g1 g2) =  `((&&&)) @@ interpretOpenGame g1 @@ interpretOpenGame g2
{-
-}
