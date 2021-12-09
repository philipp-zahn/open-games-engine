module Tests.Main

import Data.Either
import Engine.Engine
import Preprocessor.Parser
import Preprocessor.RuntimeAST
import Preprocessor.BlockSyntax
import Preprocessor.CompileBlock
import Preprocessor.CompileSyntax
import Preprocessor.Codegen

import Language.Reflection.Types

import public Control.Monad.Identity
import Preprocessor.ParserLib
import Decidable.Equality

import Control.ANSI

%language ElabReflection

opengame : (name, input : String) -> Elab ()
opengame name input =
  case parseLambdaAsOpenGame input of
       Left err => logMsg "parsing" 0 err
       Right v => logMsg "parsing" 0 "ok" -- declare [ public' (UN (Basic name)) implicitTrue
                  -- , def (UN (Basic name)) [patClause (appAll (UN (Basic name)) []) (interpretOpenGame v)]]

atomicGameInput : String
atomicGameInput = #"""
    inputs    : x ;
    feedback  :   ;

    :-----:

    inputs    : x ;
    feedback  :   ;
    operation : dependentDecision playerName (λy -> actionSpace) ;
    outputs   : y ;
    returns   : payoffFunction y x r ;

    :-----:

    outputs  : y ;
    returns  : r ;
    """#

theBlock : Block Pattern Lambda
theBlock = MkBlock
  [PVar "x"]
  []
  (pure $ MkLine [Var "x"]
                 []
                 (App (App (Var "dependentDecision") (Var "playerName")) (Lam (PVar "y") (Var "actionSpace")))
                 [PVar "y"]
                 [App (App (App (Var "payoffFunction") (Var "y")) (Var "x")) (Var "r")])

  [Var "y"]
  [PVar "r"]


Show TTImp where
  show = assert_total (show . pretty {ann=Unit})

-- jtestParse : CompileBlock.parseLambdaAsOpenGame  Main.atomicGameInput === Right {a=String} (Atom `(id))
-- jtestParse = Refl

testParseVerbose : parseVerbose Main.atomicGameInput === Right {a=String}
  (MkBlock
  [PVar "x"]
  []
  (pure $ MkLine [Var "x"]
                 []
                 (App (App (Var "dependentDecision") (Var "playerName")) (Lam (PVar "y") (Var "actionSpace")))
                 [PVar "y"]
                 [App (App (App (Var "payoffFunction") (Var "y")) (Var "x")) (Var "r")])

  [Var "y"]
  [PVar "r"])

testParseVerbose = Refl

testSame : Eq a => Show a => String -> (given, expected : a) -> IO ()
testSame desc v1 v2 = if v1 == v2 then printLn (colored Green "\{desc} : OK")
                                  else printLn (colored Red "\{desc} : FAIL")
                                    *> printLn (colored Yellow "Expected:")
                                    *> printLn v2
                                    *> printLn (colored Yellow "Got Instead:")
                                    *> printLn v1



main : IO ()
main = do printLn $ map interpretOpenGame (parseLambdaAsOpenGame atomicGameInput)
          testSame "parsingBlock"
            { given = parseVerbose atomicGameInput
            , expected = Right theBlock
            }
