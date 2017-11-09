module Main

import Data.HVect
import Data.List
import Data.String
import Data.Vect

import EnumParsing
import NumberParsing
import Schema

%default total

--We now need two parsers, one to parse a row to a schema, and one
--to parse a row given a schema.
--First, parsing schemas.
--A row schema is a comma-separated list of column schemas,
--where each column schema is a name followed by a type name in square brackets.
parseColumnType: Data.List.Elem s  ["String", "Bool", "Int", "Double"] -> ColumnType
parseColumnType {s = "String"} Here = CString
parseColumnType {s = "Bool"} (There Here) = CBool
parseColumnType {s = "Int"} (There (There Here)) = CInt
parseColumnType {s = "Double"} (There (There (There Here))) = CDouble
parseColumnType {s = _} (There (There (There (There Here)))) impossible
parseColumnType {s = _} (There (There (There (There (There _))))) impossible

IsValidType: String -> ColumnType -> Type
IsValidType s t = ValidEnum ["String", "Bool", "Int", "Double"] s parseColumnType t

isValidType: (s: String) -> Dec (t: ColumnType ** IsValidType s t)
isValidType s = isValidEnum s

--TODO: Valid identifiers.
--TODO: Tighten to a Dec, with a sensible predicate.
parseColumnSchema: (s: String) -> Maybe ColumnSchema
parseColumnSchema s =
  let (name, typeBracketed) = span (/= '[') s in
    let (_, typeRightBracket) = span (== '[') typeBracketed in
      let (typeS, bracket) = span (/= ']') typeRightBracket in
        case bracket of
          "]" =>
            case isValidType typeS of
              (Yes (t ** _)) => Just (CSchema name t)
              (No contra) => Nothing
          _ => Nothing
          
 --TODO: Fix.
parseRowSchema: (s: String) -> Maybe (n: Nat ** CSVSchema n)
parseRowSchema s = parseRowSchemaInner $ split (==',') s
  where parseRowSchemaInner : List String -> Maybe (n: Nat ** CSVSchema n)
        parseRowSchemaInner [] = Just (Z ** CSVS [])
        parseRowSchemaInner (x :: xs) =
          do c <- parseColumnSchema x
             (n ** CSVS cs) <- parseRowSchemaInner xs
             pure (S n ** CSVS (c :: cs))

ValidColumn: (s: ColumnSchema) -> String -> (ColumnData s) -> Type
ValidColumn (CSchema cName CString) = \_, _ => () --TODO: Strings could do with a spec.
ValidColumn (CSchema cName CBool) = StringIsValidBool
ValidColumn (CSchema cName CInt) = StringIsValidInt
ValidColumn (CSchema cName CDouble) = StringIsValidDouble

ColParser: ColumnSchema -> Type
ColParser x = (s: String) -> Dec (d: ColumnData x ** ValidColumn x s d)

colParser: (s: ColumnSchema) -> ColParser s
colParser (CSchema cName CString) s = Yes (s ** ())
colParser (CSchema cName CBool) s = isValidBool s
colParser (CSchema cName CInt) s = parseInt s
colParser (CSchema cName CDouble) s = parseDouble s

--We use list here rather than the tigher Vect n String, so we can more easily
--link it up to strings.
data ValidRow: (s: CSVSchema n) -> (List String) -> CSVRow s -> Type where
  NoColsValid: ValidRow (CSVS []) [] []
  ColValid: (ValidColumn col s v) -> ValidRow (CSVS cols) ss vs -> ValidRow (CSVS (col :: cols)) (s :: ss) (v :: vs)
  
invalidTailRow: ((vs: CSVRow (CSVS xs) ** ValidRow (CSVS xs) strs vs) -> Void) -> ValidRow (CSVS (x :: xs)) (str :: strs) r -> Void
invalidTailRow invalidTail (ColValid {vs} x y) = invalidTail (vs ** y)

invalidHeadRow: ((v ** ValidColumn col s v) -> Void) -> ValidRow (CSVS (col :: cols)) (s :: ss) r -> Void
invalidHeadRow invalidHead (ColValid {v} x y) = invalidHead (v ** x)

extraStrings: ValidRow (CSVS []) (s :: ss) r -> Void
extraStrings NoColsValid impossible
extraStrings (ColValid _ _) impossible

tooFewStrings: ValidRow (CSVS (col :: cols)) [] r -> Void
tooFewStrings NoColsValid impossible
tooFewStrings (ColValid _ _) impossible

decRowParser: (s: CSVSchema n) -> (strs: List String) -> Dec (r : CSVRow s ** ValidRow s strs r)
decRowParser {n = Z} (CSVS []) [] = Yes ([] ** NoColsValid)
decRowParser {n = Z} (CSVS []) (col :: cols) = No (\(_ ** prf) => extraStrings prf)
decRowParser {n = (S len)} (CSVS (col :: cols)) [] = No (\(_ ** prf) => tooFewStrings prf)
decRowParser {n = (S len)} (CSVS (col :: cols)) (s :: ss) =
  case colParser col s of
    (Yes (v ** valid)) =>
      case decRowParser (CSVS cols) ss of
        (Yes (vs ** rec)) => Yes (v :: vs ** (ColValid valid rec))
        (No contra) => No (\(_ ** prf) => invalidTailRow contra prf)
    (No contra) => No (\(_ ** prf) => invalidHeadRow contra prf)
    
StringIsValidRow: String -> CSVRow s -> Type
StringIsValidRow {s} str r = ValidRow s (split (== ',') str) r

parseRow: (s: CSVSchema n) -> (str: String) -> Dec (r: CSVRow s ** StringIsValidRow str r)
parseRow s str = decRowParser s (split (== ',') str)

partial readCsvLoop: (s: CSVSchema n) -> IO (Either String (m: Nat ** Vect m (CSVRow s)))
readCsvLoop (CSVS cols) =
  do l <- getLine
     if l == "" then
       pure (Right (Z ** []))
     else
       case parseRow (CSVS cols) l of
         (Yes (r ** prf)) =>
           do rem <- readCsvLoop (CSVS cols)
              case rem of
                (Left err) => pure $ Left err
                (Right (n ** rs)) => pure $ Right (S n ** r :: rs)
         (No contra) => pure $ Left $ "Could not parse row " ++ l

doStuffWith: Vect m (CSVRow s) -> IO ()
doStuffWith _ = putStrLn "Yup, it parses, can't actually do anything with it yet, sorry"

partial main: IO ()
main =
  do l <- getLine
     case parseRowSchema l of
       Nothing => putStrLn $ "Invalid schema " ++ l
       Just (_ ** s) =>
         do dataOrErr <- readCsvLoop s
            case dataOrErr of
              Left err => putStrLn err
              Right (_ ** dat) => doStuffWith dat
