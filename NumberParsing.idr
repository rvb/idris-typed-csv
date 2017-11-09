module NumberParsing
import Data.List
import AtMostOne

%default total

--A type-level predicate of 'one of these chars'
OneOf: String -> Char -> Type
OneOf x c = Elem c (unpack x)

--It's decidable, yay.
isOneOf: (s: String) -> (c: Char) -> Dec (OneOf s c)
isOneOf s c = isElem c (unpack s)

digits: String
digits = "0123456789"

IsDigit: Char -> Type
IsDigit = OneOf digits

decIsDigit: (c: Char) -> Dec (IsDigit c)
decIsDigit = isOneOf digits

--We can now define a safe type of strings that can be parsed to ints.
--We'll work with unpacked strings as they're much easier to work with.
data RepresentsNat : List Char -> Type where
  OneDigit: (c: Char) -> IsDigit c -> RepresentsNat [c]
  MoreDigits: (c: Char) -> IsDigit c -> RepresentsNat s -> RepresentsNat (c :: s)
  
notANatNil: (RepresentsNat []) -> Void
notANatNil (OneDigit _ _) impossible
notANatNil (MoreDigits _ _ _) impossible

startsWithNonDigit: (IsDigit c -> Void) -> RepresentsNat (c :: cs) -> Void
startsWithNonDigit contra (OneDigit c prf) = contra prf
startsWithNonDigit contra (MoreDigits c prf rec) = contra prf

remIsNotANat: (RepresentsNat (x :: xs) -> Void) -> RepresentsNat (y :: x :: xs) -> Void
remIsNotANat contra (MoreDigits c prf rec) = contra rec

representsNat: (l: List Char) -> Dec (RepresentsNat l)
representsNat [] = No notANatNil
representsNat (x :: []) =
  case decIsDigit x of
    (Yes prf) => Yes (OneDigit x prf)
    (No contra) => No (startsWithNonDigit contra)
representsNat (x :: (y :: xs)) =
  case decIsDigit x of
    (Yes prf) =>
      case representsNat (y :: xs) of
        (Yes prfrec) => Yes (MoreDigits x prf prfrec)
        (No contra) => No (remIsNotANat contra)
    (No contra) => No (startsWithNonDigit contra)

--Given nats, the step to ints is pretty easy.
data RepresentsInt: List Char -> Type where
  NatAsInt: RepresentsNat s -> RepresentsInt s
  Negative: RepresentsNat s -> RepresentsInt ('-'::s)
  
notAnIntNil: RepresentsInt [] -> Void
notAnIntNil (NatAsInt x) = notANatNil x

--This is hilarious, but I suppose it qualifies as a proof.
minusNonDigit: IsDigit '-' -> Void
minusNonDigit (There (There (There (There (There (There (There (There (There (There Here)))))))))) impossible
minusNonDigit (There (There (There (There (There (There (There (There (There (There (There _))))))))))) impossible

negativeNonNat: (RepresentsNat xs -> Void) -> RepresentsInt ('-'::xs) -> Void
negativeNonNat contra (NatAsInt (OneDigit '-' x)) = minusNonDigit x
negativeNonNat contra (NatAsInt (MoreDigits '-' x rec)) = contra rec
negativeNonNat contra (Negative x) = contra x

notNegativeNorANat: (c = '-' -> Void) -> (RepresentsNat (c :: cs) -> Void) -> RepresentsInt (c :: cs) -> Void
notNegativeNorANat notmin notnat (NatAsInt prf) = notnat prf
notNegativeNorANat notmin notnat (Negative x) = notmin Refl

--TODO: Does not support "-       42"
representsInt: (s: List Char) -> Dec (RepresentsInt s)
representsInt [] = No notAnIntNil
representsInt (x :: xs) =
  case decEq x '-' of 
    (Yes Refl) =>
      case representsNat xs of
        (Yes prf) => Yes (Negative prf)
        (No contra) => No $ negativeNonNat contra
    (No notmin) =>
        case representsNat(x :: xs) of
            (Yes prf) => Yes (NatAsInt prf)
            (No notnat) => No (notNegativeNorANat notmin notnat)

export data StringIsValidInt: String -> Int -> Type where
  IsAnInt: (s : String) -> (RepresentsInt (unpack s)) -> StringIsValidInt s (cast s)

nonIntDoesNotParse: (RepresentsInt (unpack s) -> Void) -> (i: Int ** StringIsValidInt s i) -> Void
nonIntDoesNotParse contra (x ** pf) =
  case pf of
    (IsAnInt s prf) => contra prf

export parseInt: (s: String) -> Dec (i: Int ** StringIsValidInt s i)
parseInt s =
  case representsInt (unpack s) of
    (Yes prf) => Yes (cast s ** IsAnInt s prf)
    (No contra) => No (nonIntDoesNotParse contra)


--The explicit proof is a bit of a hack in the second case,
--but is needed to allow notAPositiveDoubleNil.    
data RepresentsPositiveDouble: List Char -> Type where
   NatAsDouble: RepresentsNat cs -> RepresentsPositiveDouble cs
   Decimal: RepresentsNat cs -> RepresentsNat ds -> l = cs ++ ('.' :: ds) -> RepresentsPositiveDouble l

--The totality checker doesn't realise the Decimal case does not apply.
notAPositiveDoubleNil: RepresentsPositiveDouble [] -> Void
notAPositiveDoubleNil (NatAsDouble (OneDigit _ _)) impossible
notAPositiveDoubleNil (NatAsDouble (MoreDigits _ _ _)) impossible
notAPositiveDoubleNil (Decimal (OneDigit _ _) _ Refl) impossible
notAPositiveDoubleNil (Decimal (MoreDigits _ _ _) _ Refl) impossible

dotSeparatedListsContainDot: (cs: List Char) -> (ds: List Char) -> Elem '.' (cs ++ '.' :: ds)
dotSeparatedListsContainDot [] ds = Here
dotSeparatedListsContainDot (x :: xs) ds = There (dotSeparatedListsContainDot xs ds)

dotNonDigit: IsDigit '.' -> Void
dotNonDigit (There (There (There (There (There (There (There (There (There (There Here)))))))))) impossible
dotNonDigit (There (There (There (There (There (There (There (There (There (There (There _))))))))))) impossible

noDotsDoubleNonNat: (Elem '.' xs -> Void) -> (RepresentsNat xs -> Void) -> RepresentsPositiveDouble xs -> Void
noDotsDoubleNonNat nodots notnat (NatAsDouble nat) = notnat nat
noDotsDoubleNonNat nodots notnat (Decimal {cs} {ds} x y Refl) = nodots (dotSeparatedListsContainDot cs ds)

natContainsNoDot: RepresentsNat s -> Elem '.' s -> Void
natContainsNoDot (OneDigit '.' x) Here = dotNonDigit x
natContainsNoDot (OneDigit _ _) (There Here) impossible
natContainsNoDot (OneDigit _ _) (There (There _)) impossible
natContainsNoDot (MoreDigits '.' x z) Here = dotNonDigit x
natContainsNoDot (MoreDigits c x z) (There later) = natContainsNoDot z later

doublesContainAtMostOneDot: (AtMostOne '.' cs -> Void) -> RepresentsPositiveDouble cs -> Void
doublesContainAtMostOneDot tooManyDots (NatAsDouble x) = tooManyDots $ None $ natContainsNoDot x
doublesContainAtMostOneDot tooManyDots (Decimal {cs} {ds} x y prf) = tooManyDots $ (ExactlyOne cs (natContainsNoDot x) ds (natContainsNoDot y) $ sym prf)

nonNatWithoutDotNonDouble: (Elem '.' cs -> Void) -> (RepresentsNat cs -> Void) -> RepresentsPositiveDouble cs -> Void
nonNatWithoutDotNonDouble nodots nonat (NatAsDouble x) = nonat x
nonNatWithoutDotNonDouble nodots nonat (Decimal x y Refl) = nodots oneOccListHasAnOccurrence

equalListsEqualHeads: {l : List a} -> x :: l = y :: m -> x = y
equalListsEqualHeads Refl = Refl

equalListsEqualTails: {l : List a} -> x :: l = y :: m -> l = m
equalListsEqualTails Refl = Refl

oneOccListExtractSucc: (y :: ys) ++ (x :: m) = y :: (ys ++ x :: m)
oneOccListExtractSucc {ys = []} = Refl
oneOccListExtractSucc {ys = (x :: xs)} = Refl

eqTrans: x = y -> y = z -> x = z
eqTrans Refl Refl = Refl

uniqueEntryUnique: (Elem x l -> Void) -> (Elem x n -> Void) -> l ++ x :: m = n ++ x :: p -> (l = n, m = p)
uniqueEntryUnique {l = []} {n = []} nol non Refl = (Refl, Refl)
uniqueEntryUnique {l = []} {n = (x :: ys)} nol non Refl = void $ non Here
uniqueEntryUnique {l = (x :: ys)} {n = []} nol non Refl = void $ nol Here
uniqueEntryUnique {l = (y :: ys)} {n = (z :: xs)} nol non prf with (eqTrans (sym oneOccListExtractSucc) prf)
  uniqueEntryUnique {l = (y :: ys)} {n = (z :: xs)} nol non prf | _ with (equalListsEqualHeads prf)
    uniqueEntryUnique {l = (y :: ys)} {n = (y :: xs)} nol non prf | _ | Refl with (uniqueEntryUnique (notElemTail nol) (notElemTail non) (equalListsEqualTails prf))
      uniqueEntryUnique {l = (y :: ys)} {n = (y :: xs)} nol non prf | _ | Refl | (a, b) = (cong a, b)
      
natDoesNotEqualNonNat: cs = cs2 -> (RepresentsNat cs -> Void) -> RepresentsNat cs2 -> Void
natDoesNotEqualNonNat Refl notnat nat = notnat nat

nonAfterNatNonDouble: (Elem '.' cs -> Void) -> (Elem '.' ds -> Void) -> (RepresentsNat ds -> Void) -> (cs ++ '.' :: ds = xs) -> RepresentsPositiveDouble xs -> Void
nonAfterNatNonDouble nodotp nodota nonata Refl (NatAsDouble x) = natContainsNoDot x $ oneOccListHasAnOccurrence
nonAfterNatNonDouble nodotp nodota nonata Refl (Decimal x y prf) with (uniqueEntryUnique nodotp (natContainsNoDot x) prf)
  nonAfterNatNonDouble nodotp nodota nonata Refl (Decimal x y prf) | (a, b) = natDoesNotEqualNonNat b nonata y

nonPrefixNatNonDouble: (Elem '.' cs -> Void) -> (RepresentsNat cs -> Void) -> (Elem '.' ds -> Void) -> (cs ++ '.' :: ds = xs) -> RepresentsPositiveDouble xs -> Void
nonPrefixNatNonDouble nodotp nonatp nodota Refl (NatAsDouble x) = natContainsNoDot x $ oneOccListHasAnOccurrence
nonPrefixNatNonDouble {cs} {ds} nodotp nonatp nodota Refl (Decimal {cs=cs2} {ds=ds2} x y prf) with (uniqueEntryUnique nodotp (natContainsNoDot x) prf)
  nonPrefixNatNonDouble {cs = cs} {ds = ds} nodotp nonatp nodota Refl (Decimal {cs=cs2} {ds=ds2} x y prf) | (a, b) = natDoesNotEqualNonNat a nonatp x

representsPositiveDouble: (cs: List Char) -> Dec (RepresentsPositiveDouble cs)
representsPositiveDouble [] = No notAPositiveDoubleNil
representsPositiveDouble xs with (atMostOne '.' xs)
  representsPositiveDouble xs | (Yes (None nodots)) =
    case representsNat xs of 
      (Yes prf) => Yes (NatAsDouble prf)
      (No nonat) => No (nonNatWithoutDotNonDouble nodots nonat)
  representsPositiveDouble xs | (Yes (ExactlyOne pref f after g prf)) =
    case representsNat pref of
      (Yes prefnat) => 
        case representsNat after of
          (Yes afternat) => Yes (Decimal prefnat afternat (sym prf))
          (No contra) => No (nonAfterNatNonDouble f g contra prf)
      (No contra) => No (nonPrefixNatNonDouble f contra g prf)
  representsPositiveDouble xs | (No contra) = No (doublesContainAtMostOneDot contra)

data RepresentsDouble: List Char -> Type where
  PosDouble: RepresentsPositiveDouble cs -> RepresentsDouble cs
  NegDouble: RepresentsPositiveDouble cs -> RepresentsDouble ('-'::cs)
  
notADoubleNil: RepresentsDouble [] -> Void
notADoubleNil (PosDouble x) = notAPositiveDoubleNil x

notMinusNotDouble: (x = '-' -> Void) -> (RepresentsPositiveDouble (x :: xs) -> Void) -> RepresentsDouble (x :: xs) -> Void
notMinusNotDouble {x = x} notminus notpdouble (PosDouble y) = notpdouble y
notMinusNotDouble {x = '-'} notminus notpdouble (NegDouble y) = notminus Refl

minusThenNotDouble: (RepresentsPositiveDouble xs -> Void) -> RepresentsDouble ('-' :: xs) -> Void
minusThenNotDouble nopos (PosDouble (NatAsDouble (OneDigit '-' x))) = minusNonDigit x
minusThenNotDouble nopos (PosDouble (NatAsDouble (MoreDigits '-' x y))) = minusNonDigit x
minusThenNotDouble nopos (PosDouble (Decimal (OneDigit '-' x) y Refl)) = minusNonDigit x
minusThenNotDouble nopos (PosDouble (Decimal (MoreDigits '-' x z) y Refl)) = minusNonDigit x
minusThenNotDouble nopos (NegDouble pos) = nopos pos

representsDouble: (cs: List Char) -> Dec (RepresentsDouble cs)
representsDouble [] = No notADoubleNil
representsDouble (x :: xs) =
  case decEq x '-' of
    (Yes Refl) =>
      case representsPositiveDouble xs of
        (Yes prf) => Yes (NegDouble prf)
        (No contra) => No (minusThenNotDouble contra)
    (No nominus) =>
      case representsPositiveDouble (x :: xs) of
        (Yes prf) => Yes (PosDouble prf)
        (No nopdouble) => No (notMinusNotDouble nominus nopdouble)

--Factor out the duplication between this and the int version.
export data StringIsValidDouble: String -> Double -> Type where
  IsADouble: (s : String) -> (RepresentsDouble (unpack s)) -> StringIsValidDouble s (cast s)
  
invalidDouble: (RepresentsDouble (unpack s) -> Void) -> (d: Double ** StringIsValidDouble s d) -> Void
invalidDouble notarepresentation (_ ** IsADouble _ x) = notarepresentation x

export parseDouble: (s: String) -> Dec (d:Double **StringIsValidDouble s d)
parseDouble s =
  case representsDouble (unpack s) of
    (Yes prf) => Yes (cast s ** IsADouble s prf)
    (No contra) => No (invalidDouble contra)
