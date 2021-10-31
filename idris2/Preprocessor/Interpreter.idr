module Preprocessor.Interpreter

import Preprocessor.RuntimeAST

interface Interpreter t where
  interpret : t -> IO ()

executeOpenGame : Interpreter e => FreeOpenGame p e -> IO ()
executeOpenGame (Atom x) = interpret x
executeOpenGame (Lens x y) = ?executeOpenGame_rhs_2
executeOpenGame (Function x y) = ?executeOpenGame_rhs_3
executeOpenGame Counit = ?executeOpenGame_rhs_4
executeOpenGame (Sequential x y) = ?executeOpenGame_rhs_5
executeOpenGame (Simultaneous x y) = ?executeOpenGame_rhs_6
