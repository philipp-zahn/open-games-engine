||| Compile from the Surface language of the parser into FreeOpenGame ready for code generation
module Preprocessor.CompileSyntax

import Preprocessor.Parser -- contains the parsing functions and the surface syntax
import Preprocessor.BlockSyntax -- contains Lines and Blocks
import Preprocessor.RuntimeAST -- contains FreeOpenGame

import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Types

public export
data Pat e =
  ||| Variable pattern
    VarP Name |

  ||| Matching constructor pattern
    ConP String (List (Pat e)) |

  ||| Matching literal
    LitP e

export
Show e => Show (Pat e) where
  show (VarP n) = show n
  show (ConP n args) = "\{n} @@ \{assert_total $ show args}"
  show (LitP e) = "literal:\{assert_total $ show e}"

compileLiteral : Literal -> TTImp
compileLiteral (LInt i) = IPrimVal EmptyFC (BI i)
compileLiteral (LBool True) = `(True)
compileLiteral (LBool False) = `(False)
compileLiteral (LString str) = IPrimVal EmptyFC (Str str)


infixl 7 @@
export
(@@) : TTImp -> TTImp -> TTImp
(@@) f arg = IApp EmptyFC f arg

mutual
  compileRange : LRange -> TTImp
  compileRange (LFromR from) = `(rangeFrom) @@ (compileLambda from)
  compileRange (LFromThenR from step) = `(rangeFromThen) @@ (compileLambda from) @@ (compileLambda step)
  compileRange (LFromToR from to) = `(rangeFromTo) @@ (compileLambda from) @@ (compileLambda to)
  compileRange (LFromThenToR from step to) = `(rangeFromThenTo) @@ (compileLambda from) @@ (compileLambda step) @@ (compileLambda to)

  compileLambda : Lambda -> TTImp
  compileLambda (Lit l) = compileLiteral l
  compileLambda (Var s) = IVar EmptyFC (UN (Basic s))
  compileLambda (App f a) = IApp EmptyFC (compileLambda f) (compileLambda a)
  compileLambda (Lam pat body) =
    case compilePattern pat of
         (VarP name) => ILam EmptyFC MW ExplicitArg (Just name) (Implicit EmptyFC False) (compileLambda body)
         _ => `(id)
         -- Right clause => ?unsupprtedMatching-- ILam EmptyFC MW ExplicitArg (Just (MN "caseArg" 0)) (Implicit EmptyFC False)
         --                 --     (ICase EmptyFC (IVar EmptyFC (MN "caseArg" 0)) (compileLambda body) [clause])
  compileLambda (LList []) = `(Nil)
  compileLambda (LList (x :: xs)) = IApp EmptyFC (IApp EmptyFC `((::)) (compileLambda x)) (compileLambda (LList xs))
  -- compileLambda (LList ls) = let v = map compileLambda ls in `(ls)
  compileLambda (Do sm) = `(id)
  compileLambda (Tuple f s []) = `(MkPair) @@ compileLambda f @@ compileLambda s
  compileLambda (Tuple f s (x :: xs)) = `(MkPair) @@ compileLambda f @@ compileLambda (Tuple s x xs)
  compileLambda (Range _) = `(id)
  compileLambda (IfThenElse c t e) = `(ifThenElse) @@ compileLambda c @@ compileLambda t @@ compileLambda e
  compileLambda (IFixOp name arg1 arg2) = IVar EmptyFC (UN (Basic name)) @@ compileLambda arg1 @@ compileLambda arg2
  compileLambda (PFixOp name arg) = IVar EmptyFC (UN (Basic name)) @@ compileLambda arg
  compileLambda (LLet name val body) =
    case compilePattern name of
         (VarP name) => ILet EmptyFC EmptyFC MW name (Implicit EmptyFC True) (compileLambda val) (compileLambda body)
         _ => `(id)
         -- Right clause => ?unsupportedMatchingLet-- ICase EmptyFC (compileLambda val) (compileLambda body) [clause]
  compileLambda (Unbound name) = IHole EmptyFC name

  compilePattern : Pattern -> Pat TTImp
  compilePattern (PVar name) = VarP (UN (Basic name)) -- (IVar EmptyFC (UN (Basic name)))
  compilePattern (PCon x xs) = ConP x (map compilePattern xs)
  compilePattern (PList []) = ConP "Nil" []
  compilePattern (PList [x]) = ConP "::" [compilePattern x, ConP "Nil" []]
  compilePattern (PList (x :: y :: ys)) = ConP "::" [compilePattern x, compilePattern (PList (y :: ys))]
  compilePattern (PTuple []) = ConP "MkUnit" []
  compilePattern (PTuple [x]) = compilePattern x
  compilePattern (PTuple (x :: y :: ys)) = ConP "MkPair" [compilePattern x, compilePattern (PList (y :: ys))]
  compilePattern (PLit x) = LitP (compileLiteral x)

compLine : Line Pattern Lambda -> Line (Pat TTImp) TTImp
compLine (MkLine covOut conIn op conOut covIn) =
  MkLine  (compileLambda <$> covOut)
          (compilePattern <$> conIn)
          (compileLambda op)
          (compilePattern <$> conOut)
          (compileLambda <$> covIn)


-- Converts from the in-house AST to the template haskell AST
public export
convertGame : Block Pattern Lambda -> Block (Pat TTImp) TTImp
convertGame (MkBlock covIn conOut lns covOut conIn) =
  MkBlock (map compilePattern covIn)
          (map compileLambda conOut)
          (map compLine lns)
          (map compileLambda covOut)
          (map compilePattern conIn)

--- Should go somewehre else



-- |---------------surface level langauge ------------------| OK
--                            |-----------------Intermediate compiler representation-----------------| OK
--                                                                   |------------------code generation-------------| Doing
--            String        ->             Lines and Blocks         ->          FreeOpenGame         ->        TTImp












