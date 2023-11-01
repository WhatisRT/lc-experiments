module LAM.Parse where

import Control.Monad.Except
import LC.Base
import qualified LAM.Base as LAM
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator

import Data.Text (Text, pack, append)

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

parseTerm :: Parse Term
parseTerm = do
  (t : ts) <- sepBy1' parseTerm1 whitespace1
  return (appN t ts)

parseTerm1 :: Parse Term
parseTerm1 = parseLet <|> parseLam <|> between (string "(") (string ")") parseTerm <|> parseVar
  where
    parseVar :: Parse Term
    parseVar = Var <$> parseName

    parseLam :: Parse Term
    parseLam = do
      string "λ" >> whitespace1
      n <- parseName
      string "." >> whitespace1
      t <- parseTerm
      return (Lam n t)

    parseLet :: Parse Term
    parseLet = do
      try (string "let") >> whitespace1
      n <- parseName
      whitespace1 >> string "=" >> whitespace1
      t <- parseTerm
      whitespace1 >> string "in" >> whitespace1
      t' <- parseTerm
      return (mkLet n t t')

parseTerm' :: Text -> Either ParseError Term
parseTerm' = parse parseTerm ""


defs :: Text
defs =  "let zero = λ z. λ s. z                                                            \
      \in let suc = λ n. λ z. λ s. s n                                                      \
      \in let caseNat = λ z. λ s. λ n. n z s                                                \
      \in let fixRecNat = λ z. λ s. fix (λ rec. caseNat z (λ m. s m (rec m)))               \
      \in let add = λ n. fixRecNat n (λ k. λ rec. suc rec)                                  \
      \in let mul = λ n. fixRecNat zero (λ k. λ rec. add n rec)                             \
      \in let square = λ n. mul n n                                                         \
      \in let true = λ f. λ t. t                                                            \
      \in let false = λ f. λ t. f                                                           \
      \in let leq = fixRecNat (λ d. true) (λ d. λ rec. fixRecNat false (λ n. λ d'. rec n))  \
      \in let one = suc zero                                                                \
      \in let two = suc one                                                                 \
      \in let three = suc two                                                               \
      \in let four = square two                                                             \
      \in let eight = square two                                                            \
      \in let nine = suc eight                                                              \
      \in let ten = suc nine                                                                \
      \in let sixteen = square four                                                         \
      \in "

fromRight :: Either a b -> b
fromRight (Left _) = undefined
fromRight (Right b) = b


debug :: Term
debug = fromRight $ parseTerm' (append defs "let v = square (square two) in leq v v")

hsTermDebug :: LAM.Term
hsTermDebug = LAM.withFix $ LAM.toTerm debug


bench4 :: Term
bench4 = fromRight $ parseTerm' (append defs "let v = square (square (add ten eight)) in leq v v")

hsTermBench :: LAM.Term
hsTermBench = LAM.withFix $ LAM.toTerm bench4
