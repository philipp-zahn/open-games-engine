module Preprocessor.Codegen

import Preprocessor.RuntimeAST
import Preprocessor.CompileSyntax

import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Types

-- combineNames : List Name -> Name
-- combineNames [x] = x
-- combineNames xs = TupP xs

apply : TTImp -> List TTImp -> TTImp
apply fn [] = fn
apply fn (x :: xs) = apply (IApp EmptyFC fn x) xs

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

returnValue : List TTImp -> TTImp
returnValue [] = ?impossibleToReturnEmptyValue
returnValue (x :: []) = x
returnValue (x :: xs) = `(MkPair) @@ returnValue xs

interpretLambda : List (Pat TTImp) -> List TTImp -> TTImp
interpretLambda [] ys = ?cannotMakeLambdaFromEmptyArgList
interpretLambda ((VarP x) :: []) ys =
  ILam EmptyFC MW ExplicitArg (Just x) inferTy (returnValue ys)
interpretLambda ((ConP x xs) :: []) ys =
  ILam EmptyFC MW ExplicitArg (Just (MN "lamArg" 0)) inferTy
    (ICase EmptyFC (IVar EmptyFC (MN "lamArg"0)) inferTy
        [PatClause EmptyFC ?clause (returnValue ys)])
interpretLambda ((LitP x) :: []) ys = ?interpretLambda_rhs_7
interpretLambda (x :: (y :: xs)) ys = ?interpretLambda_rhs_4

interpretFunction : FunctionExpression (Pat TTImp) TTImp -> TTImp
interpretFunction Identity = `(id)
interpretFunction Copy = `(\x => (x, x))
interpretFunction (Lambda (MkVariables vars) (MkExpressions exps)) =
  interpretLambda vars exps

  -- ILamE (pure $ TupP vars) (TupE exps)
interpretFunction (CopyLambda (MkVariables { vars }) (MkExpressions { exps })) = ?copyu
  -- pure $ LamE (pure $ TupP vars) (TupE [TupE $ map patToExp vars, TupE exps])

interpretFunction (Multiplex (MkVariables { vars }) (MkVariables { vars = vars' })) = ?multi
  -- pure $ LamE (pure $ TupP [combineNames vars, combineNames vars']) (TupE $ map patToTTImp (vars ++ vars'))
interpretFunction (Curry f) = `(curry) @@ interpretFunction f

interpretOpenGame : FreeOpenGame (Pat TTImp) TTImp -> TTImp
interpretOpenGame (Atom n) = n
interpretOpenGame (Lens f1 f2) = `(fromLens) @@ interpretFunction f1 @@ interpretFunction f2
interpretOpenGame (Function f1 f2) = `(fromFunctions) @@ interpretFunction f1 @@ interpretFunction f2
interpretOpenGame Counit = `(counit)
interpretOpenGame (Sequential g1 g2) = `((>>>)) @@ interpretOpenGame g1 @@ interpretOpenGame g2
interpretOpenGame (Simultaneous g1 g2) =  `((&&&)) @@ interpretOpenGame g1 @@ interpretOpenGame g2
{-
-}
