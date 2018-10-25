module NumberParsing
import Data.List

import Regex

%default total

public export digit: Regex
digit = foldr (\c, r => Alt (Single c) r) Null (unpack "0123456789")

public export atLeastOne: Regex -> Regex
atLeastOne x = Conc x (Kleene x)

public export natRE: Regex
natRE = atLeastOne digit

public export intRE: Regex
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
