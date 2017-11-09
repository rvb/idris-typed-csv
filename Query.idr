module Query
--To round off the day, some ideas on how we might define query types here.

import Data.List

import Schema

unionCols: List ColumnSchema -> List ColumnSchema -> List ColumnSchema
unionCols xs ys = nub (xs ++ ys)

--Queries are either value comparisons of some sort, or refer to a specific row.
--Basic spec:
--index by row
--<=, >=, = on ints and doubles
--= on strings
--And/or/not of queries
data Query: (columnsNeeded: List ColumnSchema) -> (rowsNeeded: Nat) -> Type where
  Index: (m : Nat) -> Query [] m
  Not: Query cols n -> Query cols n
  And: Query cols1 n1 -> Query cols2 n2 -> Query (unionCols cols1 cols2) (max n1 n2)
  Or: Query cols1 n1 -> Query cols2 n2 -> Query (unionCols cols1 cols2) (max n1 n2)
