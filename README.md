# Work-in-progress typed CSV parsing in Idris

This repo is a 10% project to try and implement typed CSV parsing in Idris.
These CSVs have a header, indicating the type of each field.
Types are drawn from the set of primitive types, int, string, float and bool.
It attempts to go as far as possible towards a fully verified implementation.
As such, it includes a decidable regular expression matcher, used to parse field values.
The querying side of the problem is currently unimplemented and there are still significant gaps in the verification, particularly around parsing the file header.

# Contents

This repo contains:
- Regex.idr: The decidable regular expression matcher
- NumberParsing.idr: Decidable parsing constructs for integers and floats
- EnumParsing.idr: Decidable parsing of enum values
- Schema.idr: Types representing the schema of a typed CSV
- Main.idr: The main loop, reading and checking the file row by row. Currently, this only checks whether the file is valid.
- Query.idr: Some thoughts towards querying, currently very incomplete.