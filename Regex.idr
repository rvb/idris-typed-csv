module Regex

import Data.List

%default total

--We'll incrementally develop a regex matcher, with a decidable
--matching predicate.
data Regex: Type -> Type where
  CharR: List a -> Regex a
  
data Match: Regex a -> List a -> Type where
  CharM: Elem x xs -> Match (CharR xs) [x]

charNonEmpty: Match (CharR xs) [] -> Void
charNonEmpty (CharM _) impossible

charTooMany: Match (CharR _) (x :: y :: xs) -> Void
charTooMany (CharM _) impossible

wrongChar: (Elem x xs -> Void) -> Match (CharR xs) [x] -> Void
wrongChar nonelem (CharM elem) = nonelem elem

match: DecEq a => (re: Regex a) -> (xs: List a) -> Dec (Match re xs)
match (CharR ys) [] = No charNonEmpty
match (CharR ys) (x :: []) =
  case isElem x ys of
    (Yes prf) => Yes (CharM prf)
    (No contra) => No $ wrongChar contra
match (CharR ys) (x :: (y :: xs)) = No charTooMany
