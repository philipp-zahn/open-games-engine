module Preprocessor.Compile

import Preprocessor.Parser
import Preprocessor.Lambda
import Preprocessor.AbstractSyntax

import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Types

compileLiteral :: Literal -> Exp
compileLiteral (LInt i) = LitE $ IntegerL i
compileLiteral (LBool True) = ConE (mkName "True")
compileLiteral (LBool False) = ConE (mkName "False")
compileLiteral (LString str) = LitE $ StringL str

compileRange :: LRange -> TH.Range
compileRange (LFromR from) = FromR (compileLambda from)
compileRange (LFromThenR from step) = FromThenR (compileLambda from) (compileLambda step)
compileRange (LFromToR from to) = FromToR (compileLambda from) (compileLambda to)
compileRange (LFromThenToR from step to) = FromThenToR (compileLambda from) (compileLambda step) (compileLambda to)

compileLambda :: Lambda -> Exp
compileLambda (Lit l) = compileLiteral l
compileLambda (Var s) | isUpper (head s)  = ConE (mkName s)
                      | otherwise         = VarE (mkName s)
compileLambda (App f a) = AppE (compileLambda f) (compileLambda a)
compileLambda (Lam pat body) = LamE [compilePattern pat] (compileLambda body)
compileLambda (LList ls) = ListE $ map compileLambda ls
compileLambda (Do sm) = DoE (map toStatement sm)
  where
    toStatement :: (Maybe String, Lambda) -> Stmt
    toStatement (Nothing, lam) = NoBindS (compileLambda lam)
    toStatement (Just pat, lam) = BindS (VarP (mkName pat)) (compileLambda lam)
compileLambda (Tuple f s r) = TupE (map compileLambda (f : s : r))
compileLambda (Range range) = ArithSeqE (compileRange range)
compileLambda (IfThenElse prd thn els) = CondE (compileLambda prd) (compileLambda thn) (compileLambda els)
compileLambda (Ifix op left right) = InfixE (Just $ compileLambda left)
                                            (VarE $ mkName op)
                                            (Just $ compileLambda right)

compileLambda (PFix "-" arg) = AppE (VarE (mkName "negate")) (compileLambda arg)
compileLambda (PFix op arg) = error $ "unsupported prefix operator: " ++ op
compileLambda (LLet pat val body) = LetE [ValD (compilePattern pat)
                                               (NormalB (compileLambda val))
                                               []]
                                         (compileLambda body)
compileLambda (Unbound _) = UnboundVarE (mkName "_")


compilePattern :: Pattern -> Pat
compilePattern (PLit (LInt i)) = LitP $ IntegerL i
compilePattern (PLit (LBool True)) = ConP (mkName "True") []
compilePattern (PLit (LBool False)) = ConP (mkName "False") []
compilePattern (PLit (LString str)) = LitP $ StringL str
compilePattern (PList ls) = ListP $ fmap compilePattern ls
compilePattern (PTuple ts) = TupP $ fmap compilePattern ts
compilePattern (PVar i) = VarP (mkName i)

compLine :: ParsedLine Pattern Lambda -> ParsedLine Pat Exp
compLine (MkParsedLine covOut conIn op conOut covIn) =
  MkParsedLine  (compilePattern <$> covOut)
                (compileLambda <$> conIn)
                (compileLambda op)
                (compilePattern <$> conOut)
                (compileLambda <$> covIn)


-- Converts from the in-house AST to the template haskell AST
convertGame :: GameAST Pattern Lambda -> GameAST Pat Exp
convertGame (MkParsedBlock covIn conOut lns covOut conIn) =
  MkParsedBlock (fmap compilePattern covIn)
                (fmap compileLambda conOut)
                (fmap compLine lns)
                (fmap compilePattern covOut)
                (fmap compileLambda conIn)

compileGameLine :: ParsedLine Pat Exp -> Line Pat Exp
compileGameLine (MkParsedLine { covOut
                          , conIn
                          , op
                          , conOut
                          , covIn }) = Line covIn conOut op covOut conIn

-- convert from GameAST to Block
compileAST :: GameAST Pat Exp -> Block Pat Exp
compileAST (MkParsedBlock a b c d e) =
  Block a b (fmap compileGameLine c) e d

parseLambdaAsOpenGame :: String -> Maybe (FreeOpenGame Pat Exp)
parseLambdaAsOpenGame input =
  case parseLambda input of
    Left _ -> Nothing
    Right v -> Just $ compileBlock $ compileAST $ convertGame v


fromAST :: GameAST Pattern Lambda -> FreeOpenGame Pat Exp
fromAST = compileBlock . compileAST . convertGame

parseLambdaAsExp :: String -> Q Exp
parseLambdaAsExp input =
  either (error . show) (interpretOpenGame . fromAST) (parseLambda input)

-- A Quasiquoter for lambda expressions
game :: QuasiQuoter
game = QuasiQuoter
     { quoteExp  = parseLambdaAsExp . dropWhile isSpace
     , quotePat  = error "expected expr"
     , quoteType = error "expected expr"
     , quoteDec  = error "expected expr"
     }

parseVerboseGame :: String -> Q Exp
parseVerboseGame input =
  either (error . show) (interpretOpenGame . fromAST) (parseVerbose input)

opengame :: QuasiQuoter
opengame = QuasiQuoter
    { quoteExp  = parseVerboseGame . dropWhile isSpace
    , quotePat  = error "expected expr"
    , quoteType = error "expected expr"
    , quoteDec  = error "expected expr"
    }

-- print the parsed AST crash if it does not parse
parseAndPrintGame :: String -> String
parseAndPrintGame =  either (error . show) (show) . parseVerbose . dropWhile isSpace

printGame :: QuasiQuoter
printGame = QuasiQuoter
    { quoteExp  = \str -> [|parseAndPrintGame str|]
    , quotePat  = error "expected expr"
    , quoteType = error "expected expr"
    , quoteDec  = error "expected expr"
    }

parseAndPrintTree :: String -> String
parseAndPrintTree =  either (error . show) (show . bimap show show . fromAST) . parseVerbose . dropWhile isSpace

printTree :: QuasiQuoter
printTree = QuasiQuoter
    { quoteExp = \str -> [|parseAndPrintTree str |]
    , quotePat  = error "expected expr"
    , quoteType = error "expected expr"
    , quoteDec  = error "expected expr"
    }
