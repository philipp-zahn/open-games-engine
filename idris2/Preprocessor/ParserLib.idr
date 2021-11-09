||| A simple parser combinator library for String. Inspired by attoparsec zepto.
module Preprocessor.ParserLib

import public Data.Fin
import public Data.List
import public Data.List1
import public Data.Vect

%default total

||| data type to decide if a parser makes progress
||| A parser annotated with `Consume` always makes progress but `MayNotConsume`
||| might also make progress, it's just not guaranteed
public export
data Progress = Consumes
              | MayNotConsume

public export
(&&), (||): Progress -> Progress -> Progress
Consumes && Consumes = Consumes
_ && _ = MayNotConsume
MayNotConsume || MayNotConsume = MayNotConsume
_ || _      = Consumes

public export
andLeftAbs : (c : Progress) -> (c && MayNotConsume) === MayNotConsume
andLeftAbs Consumes = Refl
andLeftAbs MayNotConsume = Refl

public export
orRightAbs : (c : Progress) -> (c || Consumes) === Consumes
orRightAbs Consumes = Refl
orRightAbs MayNotConsume = Refl

public export
orLeftAbs : (c : Progress) -> (Consumes || c) === Consumes
orLeftAbs Consumes = Refl
orLeftAbs MayNotConsume = Refl

public export
orRightId : (c : Progress) -> (c || MayNotConsume) === c
orRightId Consumes = Refl
orRightId MayNotConsume = Refl

public export
orLeftId : (c : Progress) -> (MayNotConsume || c) === c
orLeftId Consumes = Refl
orLeftId MayNotConsume = Refl

public export
record Zipper (a : Type) where
  constructor MkZip
  prev : List a
  next : List a

public export
forward : Zipper a -> Zipper a
forward (MkZip prev []) = MkZip [] (reverse prev)
forward (MkZip prev (x :: xs)) = MkZip (x :: prev) xs

public export
backward : Zipper a -> Zipper a
backward (MkZip [] next) = MkZip (reverse next) []
backward (MkZip (x :: xs) next) = MkZip xs (x :: next)

public export
zipper : List a -> Zipper a
zipper xs = MkZip [] xs

public export
popNext : Zipper a -> Maybe a
popNext (MkZip [] []) = Nothing
popNext (MkZip ys (x :: xs)) = Just x
popNext (MkZip (y :: ys) []) = Nothing

public export
Show a => Show (Zipper a) where
  show zip = show (reverse zip.prev ++ zip.next)

||| The input state, pos is position in the string and maxPos is the length of the input string.
public export
record State where
    constructor S
    input : Zipper Char
    pos : Nat
    -- maxPos : Nat

||| advance the state by 1 character
public export
advance : State -> State
advance s = S (forward s.input) (S s.pos) -- s.maxPos

public export
Show State where
    show s = "(" ++ show (s.input) ++ ", " ++ show s.pos ++ ")"

||| Result of applying a parser
public export
data Result a = Fail Nat String | OK a State

public export
Functor Result where
  map f (Fail i err) = Fail i err
  map f (OK r s)     = OK (f r) s

public export
record Parser (consumes : Progress) (a : Type) where
    constructor P
    runParser : State -> Result a

public export
Functor (Parser c) where
  map f p = P $ \s => map f (p.runParser s)

public export
pure : a -> Parser MayNotConsume a
pure x = P $ \s => OK x s

public export
(<*>) : Parser c1 (a -> b) -> Parser c2 a -> Parser (c1 || c2) b
f <*> x = P $ \s => case (f.runParser s) of
                             OK f' s' => map f' (x.runParser s')
                             Fail i err => Fail i err

public export
(*>) : Parser c1 a -> Parser c2 b -> Parser (c1 || c2) b
p1 *> p2 = P $ \s => case p1.runParser s of
                          OK _ s' => p2.runParser s'
                          Fail i err => Fail i err

public export
(<*) : Parser c1 a -> Parser c2 b -> Parser (c1 || c2) a
(<*) p1 p2 = P $ \s => case p1.runParser s of
                            OK r s' => map (const r) (p2.runParser s')
                            Fail i err => Fail i err

public export
seqLeft : Parser c1 a -> Parser Consumes b -> Parser Consumes a
seqLeft p1 p2 = rewrite sym $ orRightAbs c1 in p1 <* p2

public export
seqRight : Parser Consumes a -> Parser c b -> Parser Consumes b
seqRight p1 p2 = p1 *> p2

public export
optRight : Parser c1 a -> Parser MayNotConsume b -> Parser c1 a
optRight p1 p2 = rewrite sym $ orRightId c1 in p1 <* p2

public export
(>>) : Parser c1 () -> Lazy (Parser c2 b) -> Parser (c1 || c2) b
p1 >> p2 = p1 *> p2

public export
empty : Parser MayNotConsume a
empty = P $ \s => Fail s.pos "no alternative left"

public export
(<|>) : Parser c1 a -> Parser c2 a -> Parser (c1 && c2) a
a <|> b = P $ \s => case (a.runParser s) of
                            OK r s' => OK r s'
                            Fail _ _ => b.runParser s


public export
(>>=) : Parser c1 a -> (a -> Parser c2 b) -> Parser (c1 || c2) b
m >>= k = P $ \s => case m.runParser s of
                         OK a s' => (k a).runParser s'
                         Fail i err => Fail i err

public export
ignore : Parser c a -> Parser c ()
ignore = map (const ())

public export
computePosAcc : Nat -> List Char -> (Int, Int) -> (Int, Int)
computePosAcc 0 input acc = acc
computePosAcc (S n) [] acc = acc
computePosAcc (S n) ('\n' :: is) (line, col) = computePosAcc n is (line + 1, 0)
computePosAcc (S n) (i :: is) (line, col) = computePosAcc n is (line, col + 1)

public export
-- compute the position as line:col
computePos : Nat -> String -> (Int, Int)
computePos pos input = computePosAcc pos (unpack input) (0,0)

||| Run a parser in a monad
||| Returns a tuple of the result and final position on success.
||| Returns an error message on failure.
public export
parse : Parser c a -> String -> Either String a
parse p str = case p.runParser (S (zipper $ unpack str) 0 ) of
                   (OK r s) => Right r
                   (Fail i err) => Left $ "Parse failed at position \{show (computePos i str)} : \{err}"


public export
parseAll : Parser c a -> String -> Either String a
parseAll p str = case p.runParser (S (zipper $ unpack str) 0) of
                      (OK r s) => if s.pos < length str then Left $ "Parse Incomplete, \{show $ length str `minus` s.pos} characters left"
                                                        else Right r
                      (Fail i err) => Left $ "Parse failed at position \{show (computePos i str)} : \{err}"

public export
parseChars : Parser c a -> List Char -> (Either String (a, Nat))
parseChars p str = case p.runParser (S (zipper $ str) 0 ) of
                    (OK r s) => Right (r, s.pos)
                    (Fail i err) => Left $ "Parse failed at position \{show i} : \{err}"


||| Combinator that replaces the error message on failure.
||| This allows combinators to output relevant errors
public export
(<?>) : Parser c a -> String -> Parser c a
(<?>) p msg = P $ \s => case p.runParser s of
                                OK r s' => OK r s'
                                Fail i _ => Fail i msg

infixl 0 <?>

||| Discards the result of a parser
public export
skip : Parser c a -> Parser c ()
skip = map (const ())

||| Maps the result of the parser `p` or returns `def` if it fails.
public export
optionMap : b -> (a -> b) -> Parser c a -> Parser MayNotConsume b
optionMap def f p = P $ \s => case p.runParser s of
                                     OK r s'  => OK (f r) s'
                                     Fail _ _ => OK def s

||| Runs the result of the parser `p` or returns `def` if it fails.
public export
option : a -> Parser c a -> Parser MayNotConsume a
option def = optionMap def id

||| Returns a Bool indicating whether `p` succeeded
public export
succeeds : Parser c a -> Parser MayNotConsume Bool
succeeds = optionMap False (const True)

||| Returns a Maybe that contains the result of `p` if it succeeds or `Nothing` if it fails.
public export
optional : Parser c a -> Parser MayNotConsume (Maybe a)
optional = optionMap Nothing Just

||| Succeeds if and only if the argument parser fails.
|||
||| In Parsec, this combinator is called `notFollowedBy`.
public export
requireFailure : Parser c a -> Parser MayNotConsume ()
requireFailure (P runParser) = P $ \s => reverseResult s $ runParser s
where
  reverseResult : State -> Result a -> Result ()
  reverseResult s (Fail _ _) = OK () s
  reverseResult s (OK _ _)   = Fail (pos s) "Purposefully changed OK to Fail"

||| Fail with some error message
public export
fail : String -> Parser c a
fail x = P $ \s => Fail s.pos x

public export
weakenProgress : Parser c a -> Parser MayNotConsume a
weakenProgress p = P $ p.runParser

||| Succeeds if the next char satisfies the predicate `f`
public export
satisfy : (Char -> Bool) -> Parser Consumes Char
satisfy f = P $ \s => case popNext s.input of
                                   Nothing => Fail s.pos "Satisfy: Unexpected end of input"
                                   Just ch => if f ch then OK ch (advance s)
                                                      else Fail s.pos "could not satisfy predicate"

public export
checkPrefix : List Char -> State -> Maybe State
checkPrefix [] st = Just st
checkPrefix (x :: xs) s = case popNext s.input of
                               Nothing => Nothing
                               Just v => if v == x then checkPrefix xs (advance s)
                                                   else Nothing

public export
data NonEmpty : String -> Type where
   MkNonEmpty : (str : String) -> ((length str > 0) === True) -> NonEmpty str


||| Succeeds if the string `str` follows.
public export
string : (str : String) -> {auto check : NonEmpty str} -> Parser Consumes String
string str = P $ \s => case checkPrefix (unpack str) s of
                            Nothing => Fail s.pos "expected string \{show str}"
                            Just st => OK str st

||| Succeeds if the end of the string is reached.
public export
eos : Parser MayNotConsume ()
eos = pure () -- P $ \s => case popNext s.input of
      --                Nothing => OK () s
      --                Just _ => Fail s.pos "expected the end of the string"

||| Succeeds if the next char is `c`
public export
char : Char -> Parser Consumes Char
char c = satisfy (== c) <?> "char " ++ show c

||| Parses a space character
public export
space : Parser Consumes Char
space = satisfy isSpace <?> "space"

||| Parses a letter or digit (a character between \'0\' and \'9\').
||| Returns the parsed character.
public export
alphaNum : Parser Consumes Char
alphaNum = satisfy isAlphaNum <?> "letter or digit"

||| Parses a letter (an upper case or lower case character). Returns the
||| parsed character.
public export
letter : Parser Consumes Char
letter = satisfy isAlpha <?> "letter"

public export
some : Parser Consumes a -> Parser Consumes (List1 a)
some p = P $ \s => case p.runParser s of
                        OK v s' => case eatMore v [] s' of
                                        (v, st') => OK v st'
                        Fail i err => Fail i err
                        where
                          eatMore : a -> List a -> State -> (List1 a, State)
                          eatMore hd tl st = case p.runParser st of
                                                  OK v s' => assert_total $ eatMore hd (v :: tl) s'
                                                  Fail i err => (hd ::: reverse tl, st)



||| Always succeeds, will accumulate the results of `p` in a list until it fails.
public export
many : Parser Consumes a -> Parser MayNotConsume (List a)
many p = (forget <$> some p) <|> pure []

||| Parse left-nested lists of the form `((init op arg) op arg) op arg`
public export
covering
hchainl : Parser c init -> Parser Consumes (init -> arg -> init) -> Parser c'' arg -> Parser c init
hchainl pini pop parg = rewrite sym $ orRightId c in pini >>= go
  where
  covering
  go : init -> Parser MayNotConsume init
  go x = (do op <- pop
             arg <- parg
             go $ op x arg) <|> pure x

||| Parse right-nested lists of the form `arg op (arg op (arg op end))`
public export
covering
hchainr : Parser c arg -> Parser Consumes (arg -> end -> end) -> Parser c' end -> Parser c' end
hchainr parg pop pend = rewrite sym $ orLeftId c' in  (<*>) {c1=MayNotConsume} {c2=c'} (go id) pend
  where
  covering
  go : (end -> end) -> Parser MayNotConsume (end -> end)
  go f = rewrite sym $ andLeftAbs (c || Consumes) in
                 (do arg <- parg
                     op <- pop
                     go $ f . op arg) <|> pure f

||| Always succeeds, applies the predicate `f` on chars until it fails and creates a string
||| from the results.
public export
covering
takeWhile : (Char -> Bool) -> Parser MayNotConsume String
takeWhile f = pack <$> many (satisfy f)

||| Similar to `takeWhile` but fails if the resulting string is empty.
public export
covering
takeWhile1 : (Char -> Bool) -> Parser Consumes String
takeWhile1 f = pack . forget <$> some (satisfy f)

-- ||| Takes from the input until the `stop` string is found.
-- ||| Fails if the `stop` string cannot be found.
-- public export
-- covering
-- takeUntil : (stop : String) -> Parser String
-- takeUntil stop = do
--     let StrCons s top = strM stop
--       | StrNil => pure ""
--     takeUntil' s top [<]
--   where
--     takeUntil' : (s : Char) -> (top : String) -> (acc : SnocList String) -> Parser String
--     takeUntil' s top acc = do
--         init <- takeWhile (/= s)
--         skip $ char s <?> "end of string reached - \{show stop} not found"
--         case !(succeeds $ string top) of
--              False => takeUntil' s top $ acc :< (init +> s)
--              True => pure $ concat {t = List} $ cast $ acc :< init


||| Parses zero or more space characters
public export
covering
spaces : Parser MayNotConsume ()
spaces = skip (many space)

||| Parses one or more space characters
public export
covering
spaces1 : Parser Consumes ()
spaces1 = skip (some space) <?> "whitespaces"

||| Discards brackets around a matching parser
public export
parens : Parser c a -> Parser Consumes a
parens p = char '(' *> (replace {p= \x => Parser x a} (orRightAbs c) (p <* char ')'))

||| Discards whitespace after a matching parser
public export
covering
lexeme : Parser c a -> Parser c a
lexeme p = rewrite sym $ orRightId c in p <* spaces

||| Matches a specific string, then skips following whitespace
public export
covering
token : (s : String) -> NonEmpty s => Parser Consumes ()
token s = lexeme (skip $ string s) <?> "token " ++ show s

public export
digits : List (Char, Fin 10)
digits = [ ('0', 0)
         , ('1', 1)
         , ('2', 2)
         , ('3', 3)
         , ('4', 4)
         , ('5', 5)
         , ('6', 6)
         , ('7', 7)
         , ('8', 8)
         , ('9', 9)
         ]
||| Matches a single digit
public export
digit : Parser Consumes (Fin 10)
digit = do x <- satisfy isDigit
           case lookup x digits of
                Nothing => fail "not a digit"
                Just y => pure y

public export
addDigit : Num a => (Fin 10 -> a) -> a -> Fin 10 -> a
addDigit f num d = 10*num + f d

public export
fromDigits : Num a => (Fin 10 -> a) -> List (Fin 10) -> a
fromDigits f [] = 0
fromDigits f (x :: xs) = addDigit f (fromDigits f xs) x
-- fromDigits f xs = foldl (addDigit f) 0 xs

public export
intFromDigits : List1 (Fin 10) -> Integer
intFromDigits = fromDigits finToInteger . forget

public export
natFromDigits : List (Fin 10) -> Nat
natFromDigits = fromDigits finToNat

||| Matches a natural number
public export
covering
natural : Parser Consumes Nat
natural = natFromDigits . forget <$> some digit

||| Matches an integer, eg. "12", "-4"
public export
covering
integer : Parser Consumes Integer
integer = do minus <- succeeds (char '-')
             x <- some digit
             pure $ if minus then (intFromDigits x)*(-1) else intFromDigits x


||| Parse repeated instances of at least one `p`, separated by `s`,
||| returning a list of successes.
|||
||| @ p the parser for items
||| @ s the parser for separators
public export
covering
sepBy1 : (parser : Parser Consumes a)
      -> (separator : Parser Consumes b)
      -> Parser Consumes (List1 a)
sepBy1 p s = [| p ::: many (s *> p) |]

||| Parse zero or more `p`s, separated by `s`s, returning a list of
||| successes.
|||
||| @ p the parser for items
||| @ s the parser for separators
public export
covering
sepBy : (p : Parser Consumes a)
     -> (s : Parser Consumes c)
     -> Parser MayNotConsume (List a)
sepBy p s = optionMap [] forget (p `sepBy1` s)

||| Parses /one/ or more occurrences of `p` separated by `comma`.
public export
covering
commaSep1 : Parser Consumes a -> Parser Consumes (List1 a)
commaSep1 p = p `sepBy1` (char ',')

||| Parses /zero/ or more occurrences of `p` separated by `comma`.
public export
covering
commaSep : Parser Consumes a -> Parser MayNotConsume (List a)
commaSep p = p `sepBy` (char ',')

-- ||| Parses alternating occurrences of `a`s and `b`s.
-- ||| Can be thought of as parsing:
-- ||| - a list of `b`s, separated, and surrounded, by `a`s
-- ||| - a non-empty list of `a`s, separated by `b`s
-- ||| where we care about the separators
-- public export
-- covering
-- alternating : Parser Consumes a
--            -> Parser Consumes b
--            -> Parser Consumes (Odd a b)
-- alternating x y = do vx <- x
--                      (vx ::) <$> [| y :: alternating x y |] <|> pure [vx]

public export
ConsumesN : Nat -> Progress
ConsumesN Z = MayNotConsume
ConsumesN _ = Consumes

||| Run the specified parser precisely `n` times, returning a vector
||| of successes.
public export
ntimes : (n : Nat) -> Parser Consumes a -> Parser (ConsumesN n) (Vect n a)
ntimes    Z  p = pure Vect.Nil
ntimes (S n) p = [| p :: (ntimes n p) |]
--
-- checkeos : ParserLib.parseChars ParserLib.eos [] === Right {a=String} ((), 0)
-- checkeos = Refl
--
-- checkEOSString : ParserLib.parse ParserLib.eos "" === Right {a=String} ((), 0)
-- checkEOSString = Refl
--
-- checkHelloStr : ParserLib.parse (ParserLib.string "hello" ) "hello" === Right {a=String} ("hello", 5)
-- checkHelloStr = Refl
--
-- checkHelloStrEnd : ParserLib.parse (ParserLib.string "hello" <* ParserLib.eos) "hello" === Right {a=String} ("hello", 5)
-- checkHelloStrEnd = Refl
--
-- checkMultiple : ParserLib.parse (ParserLib.many ParserLib.digit) "33" === Right {a=String} ([3, 3], 2)
-- checkMultiple = Refl
--
-- checkMultipleNat : ParserLib.parse (ParserLib.many ParserLib.natural) "33" === Right {a=String} ([33], 2)
-- checkMultipleNat = Refl
--
-- checkNatList : ParserLib.parse (ParserLib.many (ParserLib.natural <* ParserLib.spaces)) "33 44 1" === Right {a=String} ([33, 44, 1], 7)
-- checkNatList = Refl
--
-- checkList : ParserLib.parse (ParserLib.hchainr (ParserLib.lexeme ParserLib.natural)
--                                                (ParserLib.token "+" *> pure (+))
--                                                (ParserLib.lexeme ParserLib.natural)) "3 + 4 + 5" === Right {a=String} (12, 9)
-- checkList = Refl
--
{-
-}
