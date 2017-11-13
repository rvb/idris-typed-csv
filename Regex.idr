module Regex

import Data.List

%default total

--Regex matching based on derivatives.
--We'll start by just implementing the paper's version.
--We skip the Comp constructor, as proofs of it quickly start
--to involve non-strictly-positive constructors.
--This also works entirely on Chars to avoid weird
--type checking bugs due to interface resolution.
public export data Regex: Type where
  Empty: Regex 
  Null: Regex 
  Single: Char -> Regex
  Conc: Regex -> Regex -> Regex
  Kleene: Regex -> Regex
  Alt: Regex -> Regex -> Regex
  And: Regex -> Regex -> Regex
  
--We'll use that a regex matches a string s if and only if either:
--1) s is empty and r accepts empty strings
--2) s = "a" + t, and the derivative of r w.r.t a accepts t.
--Effectively, derivatives implement a notion of 'partial matching state'.
--Problems with this type:
--1) How do we link this to matching?
--The main problem is that trying to rely on idris
--to reduce this doesn't seem to work at all.
--That is, even if we have the result of f x,
--and pattern match on it, see it's empty, idris won't let us
--take it and claim it's Empty with Refl.
--Potential solution: Nullability proofs.
data Nullable: Regex -> Type where
  NullableEmpty: Nullable Empty
  NullableConc: Nullable x -> Nullable y -> Nullable (Conc x y)
  NullableAltL: Nullable x -> Nullable (Alt x y)
  NullableAltR: Nullable x -> Nullable (Alt y x)
  NullableKleene: Nullable (Kleene x)
  NullableAnd: Nullable x -> Nullable y -> Nullable (And x y)

nullNonNullable: Nullable Null -> Void
nullNonNullable NullableEmpty impossible
nullNonNullable (NullableConc _ _) impossible
nullNonNullable (NullableAltL _) impossible
nullNonNullable (NullableAltR _) impossible
nullNonNullable NullableKleene impossible
nullNonNullable (NullableAnd _ _) impossible

singleNonNullable: Nullable (Single x) -> Void
singleNonNullable NullableEmpty impossible
singleNonNullable (NullableConc _ _) impossible
singleNonNullable (NullableAltL _) impossible
singleNonNullable (NullableAltR _) impossible
singleNonNullable NullableKleene impossible
singleNonNullable (NullableAnd _ _) impossible

concRightNonNullable: (Nullable x -> Void) -> Nullable (Conc y x) -> Void
concRightNonNullable yn (NullableConc _ ny) = yn ny

concLeftNonNullable: (Nullable x -> Void) -> Nullable (Conc x y) -> Void
concLeftNonNullable xn (NullableConc nx ny) = xn nx

altNonNullable: (Nullable x -> Void) -> (Nullable y -> Void) -> Nullable (Alt x y) -> Void
altNonNullable xn yn (NullableAltL nx) = xn nx
altNonNullable xn yn (NullableAltR ny) = yn ny

andNonNullableL: (Nullable x -> Void) -> Nullable (And x y) -> Void
andNonNullableL xn (NullableAnd x y) = xn x

andNonNullableR: (Nullable x -> Void) -> Nullable (And y x) -> Void
andNonNullableR xn (NullableAnd y x) = xn x

nullable: (r: Regex) -> Dec (Nullable r)
nullable Empty = Yes NullableEmpty
nullable Null = No nullNonNullable
nullable (Single x) = No singleNonNullable
nullable (Conc x y) =
  case nullable x of
    Yes nx =>
      case nullable y of
        Yes ny => Yes (NullableConc nx ny)
        No yn => No (concRightNonNullable yn)
    No xn => No (concLeftNonNullable xn)
nullable (Kleene x) = Yes NullableKleene
nullable (Alt x y) =
  case nullable x of
    (Yes nx) => Yes (NullableAltL nx)
    (No xn) =>
      case nullable y of
        (Yes ny) => Yes (NullableAltR ny)
        (No yn) => No (altNonNullable xn yn)
nullable (And x y) =
  case nullable x of
    (Yes nx) =>
      case nullable y of
        (Yes ny) => Yes (NullableAnd nx ny)
        (No yn) => No (andNonNullableR yn)
    (No xn) => No (andNonNullableL xn)
    
deriv: Char -> Regex -> Regex
deriv a Empty = Null
deriv a Null = Null
deriv a (Single x) =
  case decEq a x of
    Yes _ => Empty
    No _ => Null
deriv a (Conc x y) =
  case nullable x of
    Yes _ => Alt (Conc (deriv a x) y) (deriv a y)
    No _ => Conc (deriv a x) y
deriv a (Kleene x) = Conc (deriv a x) x
deriv a (Alt x y) = Alt (deriv a x) (deriv a y)
deriv a (And x y) = And (deriv a x) (deriv a y)

data Match: List Char -> Regex -> Type where
  MatchNil: Nullable r -> Match [] r
  --The DecEq/x noise is to justify use of deriv.
  MatchCons: Match xs (deriv x r) -> Match (x :: xs) r

nilNonNullable: (Nullable r -> Void) -> (Match [] r -> Void)
nilNonNullable nope (MatchNil yes) = nope yes

remainderMismatch: (Match xs (deriv x r) -> Void) -> Match (x :: xs) r -> Void
remainderMismatch nottail (MatchCons tail) = nottail tail 

match: (s: List Char) -> (r: Regex) -> Dec (Match s r)
match [] r =
  case nullable r of
    Yes nr => Yes (MatchNil nr)
    No rn => No (nilNonNullable rn)
match (x :: xs) r =
  case match xs (deriv x r) of
    (Yes prf) => Yes (MatchCons prf)
    (No contra) => No (remainderMismatch contra)

export MatchString: String -> Regex -> Type
MatchString s r = Match (unpack s) r

export matchString: (s: String) -> (r: Regex) -> Dec (MatchString s r)
matchString s r = match (unpack s) r
