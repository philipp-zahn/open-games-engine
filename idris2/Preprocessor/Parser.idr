-- A parser for Lambda Calculus
module Preprocessor.Parser

import public Preprocessor.BlockSyntax
import Preprocessor.ParserExpr
import Preprocessor.ParserLib as P
import public Data.List1
import Generics.Derive
import Debug.Trace


tuple : List String -> String
tuple [x] = x
tuple xs = "(" ++ pack (intercalate (unpack ", ") (map unpack xs)) ++ ")"

Num a => Show a => Interpolation a where
  interpolate = show

public export
data Literal
  = LInt Integer
  | LBool Bool
  | LString String

public export
Show Literal where
  show (LInt x) = show x
  show (LBool x) = show x
  show (LString x) = x

public export
data Pattern
  = PVar String                -- Just a variable
  | PTuple (List Pattern)    -- Tuple pattern
  | PCon String (List Pattern) -- constructor pattern
  | PList (List Pattern)     -- List pattern
  | PLit Literal             -- Match a literal exactly

export
Show Pattern where
  show (PVar x) = "%\{x}"
  show (PTuple xs) = tuple (map (assert_total show) xs)
  show (PCon nm args) = #"\{assert_total $ show nm} \{concat $ intersperse " " $ assert_total (map show args)}"#
  show (PList xs) = #"[\{concat $ intersperse ", " $ assert_total (map show xs)}]"#
  show (PLit lit) = show lit

mutual
  public export
  data Lambda
    = Var String
    | App Lambda Lambda
    | Lam Pattern Lambda
    | Lit Literal
    | LList (List Lambda)
    | Do (List (Maybe String, Lambda))
    | Tuple Lambda Lambda (List Lambda)
    | Range LRange
    | IfThenElse Lambda Lambda Lambda
    | IFixOp String Lambda Lambda
    | PFixOp String Lambda
    | LLet Pattern Lambda Lambda
    | Unbound String

  -- %runElab derive "Lambda" [Generic, Meta]

  export
  Show Lambda where
    show (Var x) = "$\{x}"
    show (App x y) = "\{assert_total $ show x} \{assert_total $ show y}"
    show (Lam x y) = "λ\{assert_total $ show x}. \{assert_total $ show y}"
    show (Lit x) = assert_total $ show x
    show (LList xs) = assert_total $ show xs
    show (Do xs) = "do " ++ unlines (assert_total (map (\case (Nothing, term) => show term
                                                              (Just var, term) => "\{show var} <- \{show term}") xs))
    show (Tuple x y xs) = tuple (show x :: show y :: assert_total (map show xs))
    show (Range x) = show x
    show (IfThenElse x y z) = "if \{assert_total $ show x} then \{assert_total $ show y} else \{assert_total $ show z}"
    show (IFixOp x y z) = "\{assert_total $ show y} \{x} \{assert_total $ show z}"
    show (PFixOp x y) = "\{x} \{assert_total $ show y}"
    show (LLet x y z) = "let \{assert_total $ show x} = \{assert_total $ show y} in \{assert_total $ show z}"
    show (Unbound x) = "?" ++ x

  public export
  data LRange =
                LFromR Lambda
              | LFromThenR Lambda Lambda
              | LFromToR Lambda Lambda
              | LFromThenToR Lambda Lambda Lambda

  public export
  Show LRange where
    show (LFromR x) = "[ \{(assert_total (show x))} ..]"
    show (LFromThenR x y) = "[ \{(assert_total (show x))}, \{(assert_total (show y))} .. ]"
    show (LFromToR x y) = "[ \{(assert_total (show x))} .. \{(assert_total (show y))}]"
    show (LFromThenToR x y z) = "[ \{assert_total $ show x},{assert_total $ show y} .. \{assert_total $ show z}]"



languageKeywords : List String
languageKeywords = ["if", "then", "else", "data", "import", "do", "let", "in"
                   , "inputs", "outputs"
                   , "feedback", "returns"
                   , "operation"
                   ]


logMsg : {default 10 leading : Nat} -> String -> Parser MayNotConsume ()
logMsg msg = P $ \s => trace "\{s.pos} - \{s.pos + cast leading} : \{show $ take leading s.input.next} : \{msg}"
    $ (OK () s)

logStatus : {default 10 leading : Nat} -> Parser MayNotConsume ()
logStatus = P $ \s => trace "Log as position \{s.pos}, next \{leading} character: \{pack $ take leading s.input.next}" $ (OK () s)


-- -- traceP : Monad m => Parser a -> Parser a
-- -- traceP (P st) = trace "tracing parser" $ P $ \(S inp max pos) =>
-- --                 let () = trace "position before : \{pos}" () in
-- --                     res <- st (S inp max pos)
-- --                     () = case the (Result a) res of
-- --                         OK v st => the Unit (trace "parse succeeeded, consumed : \{take (cast (st.pos - pos))inp}" ())
-- --                         Fail newPos msg => trace "parse failed with error \{show msg}, new position is : \{newPos}" ()
-- --                  in res
--
-- -- try : Parser a -> Parser a
-- -- try (P runParser) =
-- --     P $ \st => rollbackPos st $ runParser st
-- --     where
-- --         rollbackPos : State -> Result a -> Result a
-- --         rollbackPos s (Fail a b ) = Fail s.pos b
-- --         rollbackPos s (OK a b)   = OK a b

mutual
  sepEndBy1 : Parser Consumes a -> Parser Consumes sep -> Parser Consumes (List1 a)
  sepEndBy1 p sep     = do{ x <- p
                          ; xs <- (sep *> sepEndBy p sep) <|> pure []
                          ; pure (x ::: xs)
                          }


  sepEndBy : Parser Consumes a -> Parser Consumes sep -> Parser MayNotConsume (List a)
  sepEndBy p sep = (forget <$> sepEndBy1 p sep) <|> pure []

colon : Parser Consumes ()
colon = token ":"

semi : Parser Consumes ()
semi = token ";"

choice : List (Parser Consumes a) -> Parser MayNotConsume a
choice [] = P.empty
choice (x :: xs) = x <|> choice xs

public export
oneOf : (str : List Char) -> NonEmpty str => Parser Consumes Char
oneOf xs = foldr (\x, y => x <|> y) (fail "none of \{show xs}") (map char xs)

reserved : (str : String) -> NonEmpty str => Parser Consumes ()
reserved = token -- lexeme (string name *> pure ()) -- *> requireFailure alphaNum)

reservedOp : (str : String) -> NonEmpty str => Parser Consumes ()
reservedOp op = lexeme (string op *> P.requireFailure (oneOf (unpack ":!#$%&*+./<=>?@\\^-~")))

identifier : Parser Consumes String
identifier = pack <$> (Prelude.(::) <$> letter <*> many (alphaNum <|> oneOf (unpack "_'"))) <* spaces

surround : Parser Consumes a -> Parser Consumes b -> Parser c' c -> Parser Consumes c
surround l r m = l *> m <* r

brackets : Parser c a -> Parser Consumes a
brackets = surround (char '[') (char ']')

braces : Parser c a -> Parser Consumes a
braces = surround (char '{') (char '}')

comma : Parser Consumes ()
comma = token ","

contents : Parser Consumes a -> Parser Consumes a
contents p = spaces *> p <* eos

mkInfix : (str : String) -> NonEmpty str => Parser Consumes (Lambda -> Lambda -> Lambda)
mkInfix op = reservedOp op `seqRight` pure (IFixOp op)

-- stirng literals do not escape for now
public export
stringLiteral : Parser Consumes String
stringLiteral   = lexeme (
                  do{ str <- surround (char '"')
                                      (char '"' <?> "end of string")
                                      (many stringChar)
                    ; pure (pack (foldr (maybe id (::)) [] str))
                    }
                  <?> "literal string")
    where
      stringLetter : Parser Consumes Char
      stringLetter = satisfy (\c => (c /= '"') && (c /= '\\') && (c > '\026'))

      stringChar : Parser Consumes (Maybe Char)
      stringChar = (Just <$> stringLetter)
                      -- <|> stringEscape
                      <?> "string character"

public export
operators : OperatorTable Lambda
operators = [ [Infix (mkInfix "$") AssocRight]
            , [Infix (mkInfix ">>=") AssocLeft]
            , [Infix (mkInfix "*>") AssocLeft
              ,Infix (mkInfix "<*") AssocLeft
              ,Infix (mkInfix "<*>") AssocLeft
              ,Infix (mkInfix ">") AssocLeft
              ,Infix (mkInfix "<") AssocLeft
              ,Infix (mkInfix "<=") AssocNone
              ,Infix (mkInfix ">=") AssocNone
              ]
            , [Prefix (reservedOp "-" *> pure (PFixOp "-"))]
            , [Infix (mkInfix "++") AssocRight]
            , [Infix (mkInfix "+") AssocLeft
              ,Infix (mkInfix "-") AssocLeft
              ,Infix (mkInfix "<>") AssocRight
              ]
            , [Infix (mkInfix "*") AssocLeft
              ,Infix (mkInfix "/") AssocLeft]
            ]

-- infix parser needs a parser to parse expressiosn around the operators
public export
infixParser : Parser Consumes Lambda -> Parser Consumes Lambda
infixParser lambda = buildExpressionParser Lambda operators lambda


-- ^ Parse a variable as a Lambda term
public export
variable : Parser Consumes Lambda
variable = Var <$> identifier

-- ^ Parse an Integer as a Lambda term
number : Parser Consumes Lambda
number = (pure $ Lit (LInt (cast !natural))) <?> "natural"

-- ^ Parse a string literal as a Lambda term
strLit : Parser Consumes Lambda
strLit = Lit . LString <$> stringLiteral

-- ^ Parse two things in sequence and bundle them in a pair
pair : Parser c1 a -> Parser c2 b -> Parser (c1 || c2) (a, b)
pair p1 p2 = let v =  do r1 <- p1
                         r2 <- p2
                         pure (r1, r2)
              in rewrite sym $ orRightId c2 in v

parseLit : Parser Consumes Literal
parseLit = LString <$> stringLiteral
       <|> LInt . cast <$> natural

parseUnbound : Parser Consumes Lambda
parseUnbound = reservedOp "_" *> pure (Unbound "")

isConstructor : String -> Bool
isConstructor str = case unpack str of
                         (x :: xs) => isUpper x
                         _ => False

public export
parsePattern : Parser Consumes Pattern
parsePattern =
  (identifier >>= (\p =>
      -- logMsg "found pattern identitfier : \{show p}"
      if isConstructor p then PCon p <$> many parsePattern
                         else pure $ PVar p))
  <|> PTuple <$> parens (commaSep parsePattern)
  <|> PList <$> brackets (commaSep parsePattern)
  <|> PLit <$> parseLit

public export
reduce : (a -> a -> a) -> List1 a -> a
reduce f (x ::: []) = x
reduce f (x ::: (y :: xs)) = f y (reduce f (x ::: xs))

mutual
  public export
  doNotation : Parser Consumes Lambda
  doNotation =
    Do <$> (reserved "do"
        *> braces (statement `sepEndBy` reservedOp ";"))
    where
      statement : Parser Consumes (Maybe String, Lambda)
      statement = ((Just <$> identifier <* reservedOp "<-") `pair` expr)
              <|> ((the (Maybe String) Nothing ,) <$> expr)

  parseLet : Parser Consumes Lambda
  parseLet = do
    _ <- reserved "let"
    varString <- parsePattern
    _ <- reservedOp "="
    value <- expr
    _ <- reserved "in"
    body <- expr
    pure (LLet varString value body)

  parseTuple : Parser Consumes Lambda
  parseTuple = do
    f <- expr
    _ <- comma
    s <- expr
    rest <- many (comma *> expr)
    pure (Tuple f s rest)

  public export
  lambda : Parser Consumes Lambda
  lambda = do
    _ <- reservedOp "λ"
    args <- some parsePattern
    _ <- reservedOp "->"
    body <- expr
    pure $ foldr Lam body args

  ifExp : Parser Consumes Lambda
  ifExp = do
    _ <- reserved "if"
    prd <- term
    _ <- reserved "then"
    thn <- term
    _ <- reserved "else"
    els <- term
    pure $ IfThenElse prd thn els

  public export
  ||| Parse a bracketed expression
  ||| Those are a bit complicated because they can be either a list
  ||| Or a range with begining and end
  ||| Or an infinite list
  ||| Or a range with begining and end and a step size
  ||| Or an infinite list with a step size
  bracketed : Parser MayNotConsume Lambda
  bracketed =
    (do { e1 <- expr -- first check we have at least one element
        ; do { e2 <- comma *> expr -- then expect a comma
             -- after the comma we either have more elements or …
             ; (comma *> (LList . (\x => e1 :: e2 :: x) <$> commaSep expr) <|>
             -- … or we have a range starting with `..`
               (Range <$> (reservedOp ".." *>
                                (LFromThenToR e1 e2 <$> expr <|>
                                 pure (LFromR e1))))) <|>
               pure (LList [e1, e2])
             } <|> -- if there is no comma, check if there is `..` to parse a range
               reservedOp ".." *> (Range <$> (LFromToR e1 <$> expr <|> pure (LFromR e1)))
        })
    <|> pure (LList [])

  public export
  term : Parser Consumes Lambda
  term =  parens (parseTuple <|> expr)
      <|> ifExp
      <|> lambda
      <|> variable
      <|> number
      <|> strLit
      <|> brackets bracketed
      <|> doNotation
      <|> parseLet
      <|> parseUnbound

  public export
  appl : Parser Consumes Lambda
  appl = do
    es <- some term
    pure (Parser.reduce App es)

  public export
  expr : Parser Consumes Lambda
  expr = appl <* spaces

public export
parseTwoLines : (kw1, kw2 : String) -> NonEmpty kw1 => NonEmpty kw2 =>
                Parser Consumes p -> Parser Consumes e -> Parser Consumes (List p, List e)
parseTwoLines kw1 kw2 parseP parseE =
    pair (reserved kw1 *> colon *> commaSep parseP <* semi )
         (option [] (reserved kw2 *> colon *> commaSep parseE <* semi ))
     <|> (([], ) <$> (reserved kw2 *> colon *> commaSep parseE <* semi))

public export
parseInput : Parser Consumes p -> Parser Consumes e -> Parser Consumes (List p, List e)
parseInput p1 p2 =  parseTwoLines "inputs" "feedback" p1 p2

public export
parseOutput : Parser Consumes p -> Parser Consumes e -> Parser Consumes (List p, List e)
parseOutput p1 p2 = parseTwoLines "outputs" "returns" p1 p2

public export
parseDelimiter : Parser Consumes (List1 String)
parseDelimiter = colon *> some (string "-") <* colon

public export
parseVerboseLine : Show p => Show e => Parser Consumes p -> Parser Consumes e -> Parser Consumes (Line p e)
parseVerboseLine parseP parseE = do
  (covIn, conOut) <- option ([], []) (parseInput parseE parseP)
  program <- reserved "operation" *> colon *> parseE <* semi
  (covOut,conIn) <- option ([], []) (parseOutput parseP parseE)
  pure $ MkLine covIn conOut program covOut conIn

public export
parseVerboseSyntax : Show p => Show e => Parser Consumes p -> Parser Consumes e -> Parser Consumes (Block p e)
parseVerboseSyntax parseP parseE =
  do (covIn, conOut) <- (parseInput parseP parseE <* parseDelimiter)
     lines <- some (parseVerboseLine parseP parseE)
     (covOut,conIn) <- (parseDelimiter *> parseOutput parseE parseP)
     pure $ MkBlock covIn conOut lines covOut conIn

public export
check : ParserLib.parse Parser.lambda "λx -> x" === Right {a=String} (Lam (PVar "x") (Var "x"))
check = Refl

public export
parseVerbose : String -> Either String (Block Pattern Lambda)
parseVerbose = parseAll (parseVerboseSyntax parsePattern expr)
