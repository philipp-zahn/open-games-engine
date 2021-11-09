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

Show TTImp where
  show = assert_total (show . pretty {ann=Unit})

testParse : CompileBlock.parseLambdaAsOpenGame  Main.atomicGameInput === Right {a=String} (Atom `(id))
testParse = Refl
-- %runElab (opengame "atomicGame" atomicGameInput)

main : IO ()
main = printLn $ map interpretOpenGame (parseLambdaAsOpenGame atomicGameInput)
