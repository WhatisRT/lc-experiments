module LAM.Parse where

import Data.Text (Text, append)
import LAM.Base
import qualified LC.Parse as LC

parseTerm t = toTerm <$> LC.parseTerm' t

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

termDebug :: Term
termDebug = withFix $ fromRight $ parseTerm $
  append defs "let v = square (square two) in leq v v"

bench18 :: Term
bench18 = withFix $ fromRight $ parseTerm $
  append defs "let v = square (square (add ten eight)) in leq v v"
