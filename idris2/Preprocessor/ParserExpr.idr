-- Port of https://hackage.haskell.org/package/parsec-3.1.13.0/docs/Text-Parsec-Expr.html
-- Original License	BSD-style: https://hackage.haskell.org/package/parsec-3.1.13.0/src/LICENSE

module Preprocessor.ParserExpr

import Control.Monad.Identity
import Preprocessor.ParserLib

public export
reducel : (a -> e -> a) -> a -> List e -> a
reducel f x [] = x
reducel f x (y :: xs) = reducel f (f x y) xs


public export
reducer : (e -> a -> a) -> a -> List e -> a
reducer f x [] = x
reducer f x (y :: xs) = f y (reducer f x xs)

public export
data Assoc = AssocNone
           | AssocLeft
           | AssocRight

public export
data Operator a = Infix (Parser Consumes (a -> a -> a)) Assoc
                | Prefix (Parser Consumes (a -> a))
                | Postfix (Parser Consumes (a -> a))

public export
OperatorTable : Type -> Type
OperatorTable a = List (List (Operator a))

public export
BinaryOperator : Type -> Type
BinaryOperator a = List (Parser Consumes (a -> a -> a))

public export
UnaryOperator : Type -> Type
UnaryOperator a = List (Parser Consumes (a -> a))

public export
data Ops a = BinOp (BinaryOperator a) | UnOp (UnaryOperator a)

public export
ReturnType : Type -> Type
ReturnType a = (BinaryOperator a, BinaryOperator a, BinaryOperator a, UnaryOperator a, UnaryOperator a)

public export
toParserBin : BinaryOperator a -> Parser MayNotConsume (a -> a -> a)
toParserBin [] = fail "couldn't create binary parser"
toParserBin (x :: xs) = x <|> (toParserBin xs)

public export
toParserUn : UnaryOperator a -> Parser MayNotConsume (a -> a)
toParserUn [] = fail "couldn't create unary parser"
toParserUn (x :: xs) = x <|> toParserUn xs

public export
ambiguous : (assoc : String) -> (op : Parser MayNotConsume (a -> a -> a)) -> Parser MayNotConsume a
ambiguous assoc op = (*>) {c2=MayNotConsume} op (fail ("ambiguous use of a " ++ assoc ++ " associative operator"))

mutual
  public export
  mkRassocP : (amLeft : Parser MayNotConsume a)
           -> (amNon : Parser MayNotConsume a)
           -> (rassocOp : Parser MayNotConsume (a -> a -> a))
           -> (termP : Parser Consumes a)
           -> (x : a) -> Parser MayNotConsume a
  mkRassocP amLeft amNon rassocOp termP x =
   (do f <- rassocOp
       y <- do z <- termP ; mkRassocP1 amLeft amNon rassocOp termP z
       pure (f x y))
   <|> (amLeft)
   <|> (amNon)

  public export
  mkRassocP1 : (amLeft : Parser MayNotConsume a)
            -> (amNon : Parser MayNotConsume a)
            -> (rassocOp : Parser MayNotConsume (a -> a -> a))
            -> (termP : Parser Consumes a)
            -> (x : a) -> Parser MayNotConsume a
  mkRassocP1 amLeft amNon rassocOp termP x = (mkRassocP amLeft amNon rassocOp termP x) <|> pure x

mutual
  public export
  mkLassocP : (amRight : Parser MayNotConsume a)
           -> (amNon : Parser MayNotConsume a)
           -> (lassocOp : Parser MayNotConsume (a -> a -> a))
           -> (termP : Parser Consumes a)
           -> (x : a) -> Parser MayNotConsume a
  mkLassocP amRight amNon lassocOp termP x =
    (do f <- lassocOp
        y <- termP
        mkLassocP1 amRight amNon lassocOp termP (f x y))
    <|> amRight
    <|> amNon

  public export
  mkLassocP1 : (amRight : Parser MayNotConsume a)
            -> (amNon : Parser MayNotConsume a)
            -> (lassocOp : Parser MayNotConsume (a -> a -> a))
            -> (termP : Parser Consumes a)
            -> (x : a) -> Parser MayNotConsume a
  mkLassocP1 amRight amNon lassocOp termP x = mkLassocP amRight amNon lassocOp termP x <|> pure x

public export
mkNassocP : (amRight : Parser MayNotConsume a) ->
            (amLeft : Parser MayNotConsume a) ->
            (amNon : Parser MayNotConsume a) ->
            (nassocOp : Parser MayNotConsume (a -> a -> a)) ->
            (termP : Parser Consumes a) ->
            (x : a) -> Parser Consumes a
mkNassocP amRight amLeft amNon nassocOp termP x =
  do f <- nassocOp
     y <- termP
     _ <- amRight <|> amLeft <|> amNon
     pure (f x y)

public export
splitOp : (a : Type) -> Operator a -> ReturnType a -> ReturnType a
splitOp x (Infix op AssocNone) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, op :: nassoc, prefixx, postfix)
splitOp x (Infix op AssocLeft) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, op :: lassoc, nassoc, prefixx, postfix)
splitOp x (Infix op AssocRight) (rassoc, lassoc, nassoc, prefixx, postfix) = (op :: rassoc, lassoc, nassoc, prefixx, postfix)
splitOp x (Prefix op) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, nassoc, op :: prefixx, postfix)
splitOp x (Postfix op) (rassoc, lassoc, nassoc, prefixx, postfix) = (rassoc, lassoc, nassoc, prefixx, op :: postfix)

public export
makeParser : (a : Type) -> Parser Consumes a -> List (Operator a) -> Parser Consumes a
makeParser a term ops =
  let (rassoc,lassoc,nassoc,prefixx,postfix) = reducer (splitOp a) ([],[],[],[],[]) ops
      rassocOp = toParserBin rassoc
      lassocOp = toParserBin lassoc
      nassocOp = toParserBin nassoc
      prefixxOp = toParserUn prefixx
      postfixOp = toParserUn postfix

      amRight = ambiguous "right" rassocOp
      amLeft = ambiguous "left" lassocOp
      amNon = ambiguous "non" nassocOp

      prefixxP = ParserLib.(<|>) prefixxOp (pure (\x => x))

      postfixP = ParserLib.(<|>) postfixOp (pure (\x => x))

      termP = do pre <- prefixxP
                 x <- term
                 post <- postfixP
                 pure (post (pre x))

      rassocP = mkRassocP amLeft amNon rassocOp termP
      lassocP = mkLassocP amRight amNon lassocOp termP
      nassocP = mkNassocP amRight amLeft amNon nassocOp termP
  in
      do x <- termP
         rassocP x <|> lassocP x <|> nassocP x <|> pure x <?> "operator"

public export
buildExpressionParser : (a : Type) -> OperatorTable a -> Parser Consumes a -> Parser Consumes a
buildExpressionParser a operators simpleExpr =
  reducel (makeParser a) simpleExpr operators
