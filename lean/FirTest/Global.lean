import FirTest.Layout

/-!
Tests of globals (ADR-2026-11-09-1546, ADR-2026-11-19-0124): their text,
which reads back and prints as itself, and the attributes that do not
decode; and the rules of a valid global, in memory 0 and in a memory of
16-bit units: its memory, its alignment, each unit of its initializer, each
address it takes, and its size. `crates/funk-ir/tests/global.rs` checks the
same texts, so the two parsers and the two validators agree on each.
-/

namespace FirTest

open Fir

/-- A module whose one item is the global `@g` with the attributes `as`. -/
def glob (as : String) : String := oneFunc ("data @g() " ++ as ++ " {\n}\n")

/-- A module with the layout line `l` and the global `@g` with the
attributes `as`. -/
def globIn (l as : String) : String := "layout " ++ l ++ "\n\n" ++ glob as

/-- A memory of 16-bit units with 32-bit pointers. -/
def mem16g : String := "memory(1, unit(16), pointer(32), little)"

/-- A module with the globals `@a` and `@g`, of the attributes `a` and
`g`. -/
def globs (a g : String) : String :=
  oneFunc ("data @a() " ++ a ++ " {\n}\n\ndata @g() " ++ g ++ " {\n}\n")

/-! # The text -/

#guard roundTrips (glob "size(8) align(1) constant units(104, 105, 0)")
#guard roundTrips (glob "size(0) align(1)")
#guard roundTrips (glob "size(4) align(4) constant export units(1, 0, 0, 0)")
#guard roundTrips (glob "size(16) align(8) export zeros(8) addr(@g)")
#guard roundTrips (globs "size(4) align(4) units(7) zeros(3)" "size(16) align(8) addr(@a) addr(@a, 2)")
#guard roundTrips (globIn mem16g "memory(1) size(4) align(2) units(65535) addr(@g, 1)")
#guard roundTrips (glob "size(1) align(1) units(340282366920938463463374607431768211456)")
#guard roundTrips (glob "size(18446744073709551615) align(1)")
#guard roundTrips ("data @\"a b\"() size(8) align(8) addr(@\"a b\") {\n}\n\n" ++
  oneFunc "func @f() {\n^e:\n  ret @0\n}\n")
-- A nested module holds globals of its own.
#guard roundTrips (oneFunc "module @dev() {\n  data @g() size(1) align(1) units(1) {\n  }\n\n}\n")

-- Attributes that do not decode, at the attribute; too few, at the kind.
#guard rejectedAt (glob "memory(0) size(1) align(1)") 1 11 "writes memory(N) first"
#guard rejectedAt (glob "memory(-1) size(1) align(1)") 1 11 "writes memory(N) first"
#guard rejectedAt (glob "align(1) size(1)") 1 11 "writes size(S)"
#guard rejectedAt (glob "size(-1) align(1)") 1 11 "writes size(S)"
#guard rejectedAt (glob "size(1) align(a)") 1 19 "writes align(A)"
#guard rejectedAt (glob "memory(1) size(1) align(18446744073709551616)") 1 29 "writes align(A)"
#guard rejectedAt (glob "size(1)") 1 1 "writes size(S) and align(A)"
-- `constant` comes before `export`, each once, and pieces come last.
#guard rejectedAt (glob "size(1) align(1) export constant") 1 35 "not a piece"
#guard rejectedAt (glob "size(1) align(1) constant constant") 1 37 "not a piece"
#guard rejectedAt (glob "size(1) align(1) units(1) constant") 1 37 "not a piece"
#guard rejectedAt (glob "size(1) align(1) addr(@g, 0)") 1 28 "not a piece"
#guard rejectedAt (glob "size(1) align(1) addr(g)") 1 28 "not a piece"
#guard rejectedAt (glob "size(1) align(1) units(-1)") 1 28 "not a piece"
#guard rejectedAt (glob "size(1) align(1) zeros(18446744073709551616)") 1 28 "not a piece"
#guard rejectedAt (glob "size(1) align(1) bytes(1)") 1 28 "not a piece"
#guard rejectedAt (oneFunc "data @g(%x: i8) size(1) align(1) {\n}\n") 1 9
  "a global has no parameters"
#guard rejectedAt (oneFunc "data @g() -> i8 size(1) align(1) {\n}\n") 1 14
  "a global has no results"
#guard rejectedAt (oneFunc "data @g() size(1) align(1) {\n^e:\n  ret @0\n}\n") 1 1
  "a global has an empty body"

/-! # Validation -/

#guard valid (glob "size(8) align(1) constant units(104, 105, 0)")
#guard valid (glob "size(0) align(1)")
-- A pointer of memory 0 takes 8 units there, so a table of two takes 16.
#guard valid (globs "size(4) align(4) units(7)" "size(16) align(8) addr(@a) addr(@a, 4)")
#guard valid (glob "size(16) align(8) addr(@g) addr(@g, 8)")
#guard checks (glob "size(2) align(1) units(1, 2, 3)")
  ["the initializer takes 3 units, more than the global's size, 2"]
#guard checks (glob "size(4) align(4) zeros(5)")
  ["the initializer takes 5 units, more than the global's size, 4"]
#guard checks (glob "size(8) align(8) units(1) addr(@g)")
  ["the initializer takes 9 units, more than the global's size, 8"]
#guard checks (glob "size(2) align(1) units(255, 256)")
  ["the unit 256 of the initializer does not fit in 8 bits"]
#guard checks (glob "memory(1) size(1) align(1)")
  ["the global lives in memory 1, which the data layout does not declare"]
#guard checks (glob "size(1) align(3)")
  ["the global is aligned to 3 units: an alignment is a power of two no larger than 16777215"]
#guard checks (glob "size(1) align(16777216)")
  ["the global is aligned to 16777216 units: an alignment is a power of two no larger than 16777215"]
#guard checks (glob "size(8) align(8) addr(@h)")
  ["the initializer's address of @h names no global of its table"]
-- A function's address in an initializer waits on #235.
#guard checks (oneFunc "data @g() size(8) align(8) addr(@f) {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n")
  ["the initializer's address of @f names no global of its table"]
-- A global names only globals of its own table.
#guard checks (oneFunc ("data @a() size(1) align(1) {\n}\n\n" ++
    "module @dev() {\n  data @g() size(8) align(8) addr(@a) {\n  }\n\n}\n"))
  ["the initializer's address of @a names no global of its table"]
#guard checks (oneFunc "data @f() size(1) align(1) {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n")
  ["the symbol @f names more than one item"]
-- A memory of 16-bit units: a unit up to 65535, a pointer of memory 1 in
-- two units, and one of memory 0 in four.
#guard valid (globIn mem16g "memory(1) size(3) align(2) units(65535) addr(@g, 1)")
#guard checks (globIn mem16g "memory(1) size(1) align(1) units(65536)")
  ["the unit 65536 of the initializer does not fit in 16 bits"]
#guard valid (globIn mem16g "memory(1) size(4) align(1) zeros(4)")
#guard checks ("layout " ++ mem16g ++ "\n\n" ++ globs "size(1) align(1)" "memory(1) size(3) align(1) addr(@a)")
  ["the initializer takes 4 units, more than the global's size, 3"]
-- A global of a nested module is checked against the module's one layout.
#guard checks (oneFunc "module @dev() {\n  data @g() memory(1) size(1) align(1) {\n  }\n\n}\n")
  ["the global lives in memory 1, which the data layout does not declare"]

end FirTest
