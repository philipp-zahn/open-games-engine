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

-- patToTTImp : Name -> TTImp
-- patToTTImp (VarP e) = VarE e
-- patToTTImp (TupP e) = TupE (map patToTTImp e)
-- patToTTImp (LitP e) = LitE e
-- patToTTImp (ListP e) = ListE (fmap patToTTImp e)
-- patToTTImp (ConP n e) = apply (VarE n) (fmap patToTTImp e)

interpretFunction : FunctionExpression Name TTImp -> TTImp
interpretFunction Identity = `(id)
interpretFunction Copy = `(\x => (x, x))
interpretFunction (Lambda (MkVariables {vars}) (MkExpressions {exps})) = ?lam
  -- ILamE (pure $ TupP vars) (TupE exps)
interpretFunction (CopyLambda (MkVariables { vars }) (MkExpressions { exps })) = ?copyu
  -- pure $ LamE (pure $ TupP vars) (TupE [TupE $ map patToExp vars, TupE exps])

interpretFunction (Multiplex (MkVariables { vars }) (MkVariables { vars = vars' })) = ?multi
  -- pure $ LamE (pure $ TupP [combineNames vars, combineNames vars']) (TupE $ map patToTTImp (vars ++ vars'))
interpretFunction (Curry f) = `(curry) @@ interpretFunction f

interpretOpenGame : FreeOpenGame Name TTImp -> TTImp
interpretOpenGame (Atom n) = n
interpretOpenGame (Lens f1 f2) = `(fromLens) @@ interpretFunction f1 @@ interpretFunction f2
interpretOpenGame (Function f1 f2) = `(fromFunctions) @@ interpretFunction f1 @@ interpretFunction f2
interpretOpenGame Counit = `(counit)
interpretOpenGame (Sequential g1 g2) = `((>>>)) @@ interpretOpenGame g1 @@ interpretOpenGame g2
interpretOpenGame (Simultaneous g1 g2) =  `((&&&)) @@ interpretOpenGame g1 @@ interpretOpenGame g2
{-
-}
