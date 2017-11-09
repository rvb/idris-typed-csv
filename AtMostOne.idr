module AtMostOne

import Data.List

%default total

public export data AtMostOne: (x : a) -> List a -> Type where
  None: (Elem x l -> Void) -> AtMostOne x l
  ExactlyOne: (pref: List a) -> (Elem x pref -> Void) -> (after: List a) -> (Elem x after -> Void) -> (pref ++ x :: after = l) -> AtMostOne x l
  
notElemNil: Elem x [] -> Void
notElemNil Here impossible
notElemNil (There _) impossible

notElemRec: (Elem x l -> Void) -> (x = y -> Void) -> Elem x (y :: l) -> Void
notElemRec nottail nothead Here = nothead Refl
notElemRec nottail nothead (There later) = nottail later

export notElemTail: (Elem x (y :: l) -> Void) -> Elem x l -> Void
notElemTail nowhere intail = nowhere (There intail)

notAtMostOneRec: (AtMostOne x l -> Void) -> AtMostOne x (y :: l) -> Void
notAtMostOneRec nope (None g) = nope $ None $ notElemTail g
notAtMostOneRec {y = x} nope (ExactlyOne [] f after notafter Refl) = nope (None notafter)
notAtMostOneRec {y = z} nope (ExactlyOne (z :: xs) f after g Refl) = nope (ExactlyOne xs (notElemTail f) after g Refl)

export oneOccListHasAnOccurrence: Elem x (pref ++ x :: after)
oneOccListHasAnOccurrence {pref = []} = Here
oneOccListHasAnOccurrence {pref = (x :: xs)} = There oneOccListHasAnOccurrence

notAtMostOneIfInTail: (Elem x l) -> (AtMostOne x (x :: l)) -> Void
notAtMostOneIfInTail prf (None nowhere) = nowhere Here
notAtMostOneIfInTail prf (ExactlyOne [] _ after notafter Refl) = notafter prf
notAtMostOneIfInTail prf (ExactlyOne (y :: xs) notpref after _ Refl) = notpref Here

export atMostOne: (DecEq a) => (x : a) -> (l: List a) -> Dec (AtMostOne x l)
atMostOne x [] = Yes (None notElemNil)
atMostOne x (y :: xs) =
  case decEq x y of
    (Yes Refl) =>
      case atMostOne x xs of
        (Yes (None nottail)) => Yes (ExactlyOne [] notElemNil xs nottail Refl)
        (Yes (ExactlyOne pref notbefore after notafter Refl)) => No (notAtMostOneIfInTail (oneOccListHasAnOccurrence))
        (No contra) => No (notAtMostOneRec contra)
    (No nothead) =>
      case atMostOne x xs of
        (Yes (None nottail)) => Yes (None (notElemRec nottail nothead))
        (Yes (ExactlyOne pref notpref after notafter prf)) => Yes (ExactlyOne (y :: pref) (notElemRec notpref nothead) after notafter (cong prf))
        (No contra) => No (notAtMostOneRec contra)
