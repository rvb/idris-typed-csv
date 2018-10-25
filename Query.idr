module Query

import Data.Vect

import Schema

data Expr: CSVSchema n -> Type -> Type where
  LitInt: Expr s Int
  --Similar literals for other types (Double, bool,string)
  IntColumn: (n: String) -> Data.Vect.Elem (CSchema n CInt) s -> Expr (CSVS s) Int
  --Same for other types.
  --Operators, i.e.:
  Leq: Expr s Int -> Expr s Int -> Expr s Bool

matches: Expr s Bool -> CSVRow s -> Bool

partition: (f: x -> Bool) -> Vect m x -> (k ** l ** Vect k ((v:x) ** So (f x)) ** Vect l ((v: x) ** So (not (f x))) ** k + l = m)

choose: (b: Bool) -> Either (So b) (So (not b))

filter: Vect m (CSVRow s) -> (query: Expr s Bool) -> (n : Nat ** Vect n (r:CSVRow s ** So (matches query r)))
