module Tests.Main

import Engine.Engine
import Preprocessor.Parser

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
main : IO ()
main = print (parseVerbose atomicGameInput)
