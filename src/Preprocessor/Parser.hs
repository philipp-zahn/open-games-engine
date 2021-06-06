{-# LANGUAGE DeriveFunctor #-}
module Preprocessor.Parser where

import Text.Parsec
import Text.Parsec.String
import Preprocessor.Lambda

type GameAST p e = ParsedBlock p e (ParsedLine p e)

word :: Parser String
word = many1 alphaNum

quoted :: Parser String
quoted = char '"' *> manyTill anyChar (char '"')

uncurry5 :: (a -> b -> c -> d -> e -> f) -> (a, b, c, d, e) -> f
uncurry5 f (x, y, z, w, v) = f x y z w v

lineSep :: String-> Parser ()
lineSep str = spaces <* string str <* spaces

-- A parser for GameAST
gameASTParser :: Parser (GameAST Pattern Lambda)
gameASTParser =  parseBlock parsePattern expr (parseLine parsePattern expr) <* eof

-- parse a string into a GameAST
parseLambda :: String -> Either ParseError (GameAST Pattern Lambda)
parseLambda = parse gameASTParser "game AST parser"

-- parse a verbose syntax into a GameAST
parseVerbose :: String -> Either ParseError (GameAST Pattern Lambda)
parseVerbose = parse (parseVerboseSyntax parsePattern expr (parseVerboseLine parsePattern expr)) "verbose parser"
