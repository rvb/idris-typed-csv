module Schema

import Data.HVect
import Data.Vect

public export data ColumnType =
  CString | CBool | CInt | CDouble

Eq ColumnType where
  (==) CString CString = True
  (==) CBool CBool = True
  (==) CInt CInt = True
  (==) CDouble CDouble = True
  (==) _ _ = False

public export record ColumnSchema where
  constructor CSchema
  cName : String
  cType : ColumnType

export Eq ColumnSchema where
  (==) (CSchema n1 t1) (CSchema n2 t2) = n1 == n2 && t1 == t2

--A CSV Schema is a sequence of column schemas, with a fixed length.
public export data CSVSchema: Nat -> Type where
  CSVS: (Vect n ColumnSchema) -> CSVSchema n
  
public export ColumnData: ColumnSchema -> Type
ColumnData (CSchema _ CString) = String
ColumnData (CSchema _ CBool) = Bool
ColumnData (CSchema _ CInt) = Int
ColumnData (CSchema _ CDouble) = Double

--Now, we need to compute the type of a row in our CSV, according to a given schema.
public export CSVRow: CSVSchema n -> Type
CSVRow (CSVS xs) = HVect (map ColumnData xs)

