module EnumParsing

import Data.List

%default total

export data ValidEnum: (values: List String) -> (s: String) -> (f: Elem s values -> a) -> a -> Type where
  ValidEnumValue: (s : String) -> (prf: Elem s values) -> ValidEnum values s f (f prf)
  
--We don't need the implicit s, this is just to clarify the value we're looking at.
parseBool: (Elem s ["True", "False"]) -> Bool
parseBool {s = "True"} Here = True
parseBool {s = "False"} (There Here) = False
parseBool {s = _} (There (There Here)) impossible
parseBool {s = _} (There (There (There _))) impossible

export StringIsValidBool: String -> Bool -> Type
StringIsValidBool s b = ValidEnum ["True", "False"] s (parseBool) b

invalidEnum: (Elem s values -> Void) -> (val ** ValidEnum values s f val) -> Void
invalidEnum contra (_ ** ValidEnumValue s prf) = contra prf

export isValidEnum: {values: List String} -> (s: String) -> Dec (val ** ValidEnum values s f val)
isValidEnum {f} {values} s =
   case isElem s values of
     (Yes prf) => Yes (f prf ** ValidEnumValue s prf)
     (No contra) => No (invalidEnum contra)

--Bizarrely, we can't eta-reduce this.
export isValidBool: (s: String) -> Dec (b: Bool ** StringIsValidBool s b)
isValidBool s = isValidEnum s
