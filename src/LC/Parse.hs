-- | Parsing lambda terms.
module LC.Parse (parseTerm) where

import LC.Base

import Data.Text (Text, pack, append)
import Text.Parsec

type Parse = Parsec Text ()

keywords :: [Name]
keywords = map pack ["let", "in"]

whitespace1 = skipMany1 space

sepBy1' :: Parse a -> Parse b -> Parse [a]
sepBy1' pa pb = do
  a <- pa
  as <- many (try (pb >> pa))
  return (a : as)

parseName :: Parse Name
parseName = do
  n <- many1 (noneOf ['(', ')', 'λ', '.', ';', '=', ' ', '\n'])
  if pack n `elem` keywords
    then fail (n ++ " can not be a name since it is a keyword!")
    else return (pack n)

parseTermN :: Parse Term
parseTermN = do
  (t : ts) <- sepBy1' parseTerm1 whitespace1
  return (appN t ts)

parseTerm1 :: Parse Term
parseTerm1 = parseLet <|> parseLam <|> between (string "(") (string ")") parseTermN <|> parseVar
  where
    parseVar :: Parse Term
    parseVar = Var <$> parseName

    parseLam :: Parse Term
    parseLam = do
      string "λ" >> whitespace1
      n <- parseName
      string "." >> whitespace1
      t <- parseTermN
      return (Lam n t)

    parseLet :: Parse Term
    parseLet = do
      try (string "let") >> whitespace1
      n <- parseName
      whitespace1 >> string "=" >> whitespace1
      t <- parseTermN
      whitespace1 >> string "in" >> whitespace1
      t' <- parseTermN
      return (mkLet n t t')

-- | Parse a term from a string.
parseTerm :: Text -> Either ParseError Term
parseTerm = parse parseTermN ""
