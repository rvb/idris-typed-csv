module NumberParsing
import Data.List
import AtMostOne

import Regex

%default total

digit: Regex
digit = foldr (\c, r => Alt (Single c) r) Null (unpack "0123456789")

atLeastOne: Regex -> Regex
atLeastOne x = Conc x (Kleene x)

natRE: Regex
natRE = atLeastOne digit

intRE: Regex
intRE = Conc (Alt Empty (Single '-')) natRE

export data StringIsValidInt: String -> Int -> Type where
   IsAnInt: (s : String) -> (MatchString s NumberParsing.intRE) -> StringIsValidInt s (cast s)
   
mismatchNotInt: (MatchString s NumberParsing.intRE -> Void) -> (i**StringIsValidInt s i) -> Void
mismatchNotInt mismatch (_ ** pf) =
  case pf of
    (IsAnInt _ match) => mismatch match

export parseInt: (s: String) -> Dec (i: Int ** StringIsValidInt s i)
parseInt s =
  case matchString s intRE of
    (Yes prf) => Yes (cast s ** IsAnInt s prf)
    (No contra) => No (mismatchNotInt contra)

--TODO: Doubles.
doubleRE: Regex
doubleRE = Conc intRE (Alt Empty (Conc (Single '.') natRE))

export data StringIsValidDouble: String -> Double -> Type where
  IsADouble: (s: String) -> MatchString s NumberParsing.doubleRE -> StringIsValidDouble s (cast s)

mismatchNotDouble: (MatchString s NumberParsing.doubleRE -> Void) -> (d ** StringIsValidDouble s d) -> Void
mismatchNotDouble mismatch (_ ** pf) =
  case pf of
    (IsADouble s match) => mismatch match

export parseDouble: (s: String) -> Dec (d: Double ** StringIsValidDouble s d)
parseDouble s =
  case matchString s doubleRE of
    (Yes prf) => Yes (cast s ** IsADouble s prf)
    (No contra) => No (mismatchNotDouble contra)
