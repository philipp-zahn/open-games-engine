module Tests.Main

import Engine.Engine
import Preprocessor.Parser
import Preprocessor.RuntimeAST
import Preprocessor.BlockSyntax
import Preprocessor.CompileBlock
import Preprocessor.CompileSyntax
import Preprocessor.Codegen

import Language.Reflection.Types

atomicGameInput : String
atomicGameInput = #"""
    inputs    : x ;
    feedback  :   ;

    :-----:

    inputs    : x ;
    feedback  :   ;
    operation : dependentDecision playerName (\y -> actionSpace) ;
    outputs   : y ;
    returns   : payoffFunction y x r ;

    :-----:

    outputs  : y ;
    returns  : r ;
    """#

Show TTImp where
  show = show . pretty {ann=Unit}

main : IO ()
main = printLn (parseLambdaAsOpenGame atomicGameInput)
