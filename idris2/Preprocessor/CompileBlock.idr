||| Compiles FreeOpenGame into RuntimeAST
module Preprocessor.CompileBlock

import Preprocessor.CompileSyntax
import Preprocessor.BlockSyntax
import Preprocessor.Parser
import Preprocessor.RuntimeAST
import Data.List
import Data.Vect

import Language.Reflection.Types

--- Specialised Lines ready for compilation
SLine : Type
SLine = Line Name TTImp

||| A Line along with its covariant and contravariant context
record LineWithContext (p, e : Type) where
  constructor MkLineCtx
  line : Line p e
  covariantContext : Variables p
  contravariantContext : Variables p


-- The business end of the compiler

compileLine : LineWithContext p e -> FreeOpenGame p e
compileLine (MkLineCtx l cov con) = 
  let l1 = Function (CopyLambda cov (MkExpressions (covariantInputs l))) (Multiplex con (MkVariables (contravariantOutputs l)))
      l2 = Simultaneous (Function Identity Identity) (Atom (matrix l))
      l3 = Function (Multiplex cov (MkVariables $ (covariantOutputs l)))
                     (CopyLambda con (MkExpressions (contravariantInputs l)))
   in Sequential (Sequential l1 l2 )  l3

||| Vector version of `tails` carrying the size information
||| `tails` returns all the postfixes of the vector, from largest to smallest
tailsVect : Vect n a -> Vect (S n) (List a)
tailsVect xs = toList xs :: (case xs of {[] => []; _ :: xs' => tailsVect xs'})

||| Vector version of `inits` carrying the size information
||| `inits` generate all the prefixes of the vector, from smallest to largest
initsVect : Vect n a -> Vect (S n) (List a)
initsVect [] = [[]]
initsVect (x :: xs) =  [] :: map (x ::) (initsVect xs)

||| Vector verion of `init` carrying the size information
||| `init` drops the last value of the vector
initVect : Vect (S n) a -> Vect n a
initVect (x :: []) = []
initVect (x :: (y :: xs)) = x :: initVect (y :: xs)

||| Convert a non-empty list into a vector
list1ToVect : List1 a -> (n ** Vect (S n) a)
list1ToVect (head ::: []) = (0 ** [head])
list1ToVect (head ::: (x :: xs)) =
  let (nr ** lr) = list1ToVect (x ::: xs) in
      (S nr ** head :: lr)

||| Convert a non-empty vector into a non-empty list
vectToList1 : Vect (S n) a -> List1 a
vectToList1 (x :: xs) = x ::: toList xs

||| Extract all the covariant variables from each line inside the block
covariantContexts : Block p e -> List1 (Variables p)
covariantContexts block = 
    let f = \contexts => flattenVariables (MkVariables (blockCovariantInputs block) :: contexts)
     in vectToList1 $ map f (initVect (initsVect (map (MkVariables . covariantOutputs) (DPair.snd $ list1ToVect $ blockLines block))))

||| extract all the contravariant variables from each line inside the block
contravariantContexts : Block p e -> List1 (Variables p)
contravariantContexts block = 
    vectToList1 $ map (f . reverse) (tail (tailsVect (map (MkVariables . contravariantOutputs) (DPair.snd $ list1ToVect $ blockLines block))))
    where f : List (Variables p) -> Variables p
          f contexts = flattenVariables (concat {t=List} 
                                                   [ pure (MkVariables (blockCovariantInputs block))
                                                   , map (MkVariables . covariantOutputs) (forget $ blockLines block)
                                                   , pure (MkVariables (blockContravariantInputs block))
                                                   , contexts])

||| Convert a block into a list of lines along with the context surrounding them
linesWithContext : Block p e -> List1 (LineWithContext p e)
linesWithContext block = zipWith3 MkLineCtx (blockLines block) (covariantContexts block) (contravariantContexts block)

||| Compile a block into a FreeOpenGame, ready for code generation
export
compileBlock : Block p e -> FreeOpenGame p e
compileBlock block = 
    let lines = the (List1 (LineWithContext p e)) (linesWithContext block)
        covariantBlockContext = flattenVariables 
          [ covariantContext (last lines) , MkVariables (covariantOutputs (line (last lines)))]
        contravariantBlockContext = flattenVariables [contravariantContext (head lines)
                                                     , MkVariables (contravariantOutputs (line (head lines)))]
        l1 = Function Identity (Lambda contravariantBlockContext (MkExpressions (blockContravariantOutputs block)))
        l2 = foldl1 Sequential (map compileLine lines)
        l3 = Lens (Lambda covariantBlockContext (MkExpressions (blockCovariantOutputs block)))
                  (Curry (Multiplex covariantBlockContext (MkVariables (blockContravariantInputs block))))
     in Sequential (Sequential l1 l2) l3

||| Parses a game and compiels it down to a `FreeOpenGame` ready for code generation
export
parseLambdaAsOpenGame : String -> Either String (FreeOpenGame Name TTImp)
parseLambdaAsOpenGame = map (compileBlock . convertGame) . parseVerbose

-- print the parsed AST crash if it does not parse
||| parses a game and returns a string representing the AST or, representing and error
||| Useful for debugging
export
parseAndPrintGame : String -> String
parseAndPrintGame =  either (id) (show) . parseVerbose 
