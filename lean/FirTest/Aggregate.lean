import FirTest.Layout
import Fir.Execution.RunItems

/-!
Tests of aggregates' layouts (ADR-2026-11-16-1546): their text, which reads
back and prints as itself, and the attributes that do not decode; and the
rules of a valid layout, in memory 0 and in a memory of 16-bit units, among
them the spacing of a repeated field's elements (the human's ruling of
2026-11-16 on #236); and the layouts as a run gives them to each op.
`crates/funk-ir/tests/aggregate.rs` checks the same texts, so the two
parsers and the two validators agree on each.
-/

namespace FirTest

open Fir

/-- A module whose one item is the aggregate `@s` with the attributes
`as`. -/
def agg (as : String) : String := oneFunc ("aggregate @s() " ++ as ++ " {\n}\n")

/-- A module with the layout line `l` and the aggregate `@s` with the
attributes `as`. -/
def aggIn (l as : String) : String := "layout " ++ l ++ "\n\n" ++ agg as

/-- The pair of an `i64` and a pointer in memory 0. -/
def pair : String := "memory(0) size(16) align(8) field(0, i64) field(8, ptr)"

/-- A memory of 16-bit units with 32-bit pointers. -/
def mem16 : String := "memory(1, unit(16), pointer(32), little)"

/-- The problem of the field at offset `o` of `@s`. -/
def fieldAt (o : Nat) (s : String) : String := "the field at offset " ++ toString o ++ " " ++ s

/-! # The text -/

#guard roundTrips (agg pair)
#guard roundTrips (agg "memory(0) size(16) align(4) field(0, i24, 4)")
#guard roundTrips (agg "memory(0) size(0) align(1)")
#guard roundTrips (agg "memory(0) size(4) align(4) field(0, i32) field(4, i32, 0)")
#guard roundTrips (agg "memory(0) size(18446744073709551615) align(1)")
#guard roundTrips (aggIn mem16 "memory(1) size(4) align(2) field(0, ptr(1)) field(2, i16)")
#guard roundTrips ("aggregate @\"a b\"() memory(0) size(1) align(1) field(0, i8) {\n}\n\n" ++
  oneFunc "func @f() {\n^e:\n  ret @0\n}\n")
-- A nested module holds layouts of its own.
#guard roundTrips (oneFunc ("module @dev() {\n  aggregate @s() " ++ pair ++ " {\n  }\n\n}\n"))

-- Attributes that do not decode, at the attribute; a header that is not
-- one, at the kind.
#guard rejectedAt (agg "size(16) memory(0) align(8)") 1 16 "writes memory(N) first"
#guard rejectedAt (agg "memory(0) size(-1) align(8)") 1 26 "writes size(S) second"
#guard rejectedAt (agg "memory(0) size(18446744073709551616) align(1)") 1 26 "size(S)"
#guard rejectedAt (agg "memory(0) size(16) align(a)") 1 35 "writes align(A) third"
#guard rejectedAt (agg "memory(0) size(16)") 1 1 "writes memory(N), size(S) and align(A)"
#guard rejectedAt (agg "memory(0) size(16) align(8) field(0)") 1 44 "not a field"
#guard rejectedAt (agg "memory(0) size(16) align(8) field(0, 5)") 1 44 "not a field"
#guard rejectedAt (agg "memory(0) size(16) align(8) field(0, i8, 1, 2)") 1 44 "not a field"
#guard rejectedAt (agg "memory(0) size(16) align(8) field(0, i0x)") 1 44 "not a field"
#guard rejectedAt (agg "memory(0) size(16) align(8) field(-1, i8)") 1 44 "not a field"
#guard rejectedAt (agg "memory(0) size(16) align(8) fields(0, i8)") 1 44 "not a field"
#guard rejectedAt (oneFunc "aggregate @s(%x: i8) memory(0) size(1) align(1) {\n}\n") 1 14
  "an aggregate has no parameters"
#guard rejectedAt (oneFunc "aggregate @s() -> i8 memory(0) size(1) align(1) {\n}\n") 1 19
  "an aggregate has no results"
#guard rejectedAt
  (oneFunc "aggregate @s() memory(0) size(1) align(1) {\n^e:\n  ret @0\n}\n") 1 1
  "an aggregate has an empty body"

/-! # Validation -/

#guard valid (agg pair)
#guard valid (agg "memory(0) size(0) align(1)")
-- A repeated field's elements are rounded up to their alignment: four
-- `i24` take 16 units of memory 0, not 12.
#guard valid (agg "memory(0) size(16) align(4) field(0, i24, 4)")
#guard checks (agg "memory(0) size(12) align(4) field(0, i24, 4)")
  [fieldAt 0 "ends past the layout's size, 12"]
#guard checks (agg "memory(0) size(16) align(4) field(0, i24, 4) field(12, i8)")
  ["two fields of the layout share a unit"]
-- A field of no elements, as a C flexible array member, takes no units.
#guard valid (agg "memory(0) size(4) align(4) field(0, i32) field(4, i32, 0)")
#guard valid (agg "memory(0) size(4) align(4) field(0, i32) field(0, i32, 0)")
-- Overlapping and misaligned fields, a field past the size, and an
-- alignment that is not a power of two.
#guard checks (agg "memory(0) size(16) align(8) field(0, i64) field(4, i32)")
  ["two fields of the layout share a unit"]
#guard checks (agg "memory(0) size(16) align(8) field(4, i64)")
  [fieldAt 4 "is not a multiple of its type's alignment, 8"]
#guard checks (agg "memory(0) size(8) align(8) field(4, i64)")
  [fieldAt 4 "is not a multiple of its type's alignment, 8",
   fieldAt 4 "ends past the layout's size, 8"]
#guard checks (agg "memory(0) size(16) align(4) field(0, i64)")
  [fieldAt 0 "has a type aligned to 8 units, more than the layout's 4"]
#guard checks (agg "memory(0) size(12) align(6)")
  ["the layout is aligned to 6 units: an alignment is a power of two no larger than 16777215"]
#guard checks (agg "memory(0) size(1) align(0)")
  ["the layout is aligned to 0 units: an alignment is a power of two no larger than 16777215"]
-- A memory that the module does not declare, and a field's type that names
-- one, or is not valid, or may not be a field.
#guard checks (agg "memory(1) size(4) align(4) field(0, i32)")
  ["the layout describes memory 1, which the data layout does not declare"]
#guard checks (agg "memory(0) size(8) align(8) field(0, ptr(1))")
  ["a type names memory 1, which the data layout does not declare"]
#guard checks (agg "memory(0) size(4) align(4) field(0, i0)")
  ["a type of the layout is not valid"]
#guard checks (agg "memory(0) size(4) align(4) field(0, f32)")
  [fieldAt 0 "has a type that may not be a field: an integer or a pointer"]
-- Two items share no symbol.
#guard checks (oneFunc ("aggregate @f() " ++ pair ++ " {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n"))
  ["the symbol @f names more than one item"]

-- A memory of 16-bit units: `i16` takes one unit, `i32` two, a pointer of
-- memory 1 two, and one of memory 0 four, aligned to 4.
#guard valid (aggIn mem16 "memory(1) size(4) align(2) field(0, ptr(1)) field(2, i16)")
#guard valid (aggIn mem16 "memory(1) size(8) align(4) field(0, ptr, 2)")
#guard checks (aggIn mem16 "memory(1) size(6) align(4) field(2, ptr)")
  [fieldAt 2 "is not a multiple of its type's alignment, 4"]
#guard valid (aggIn mem16 "memory(1) size(6) align(2) field(0, i24, 2)")
#guard checks (aggIn mem16 "memory(1) size(3) align(2) field(0, i24, 2)")
  [fieldAt 0 "ends past the layout's size, 3"]
-- An entry that aligns the memory's pointers aligns its pointer fields.
#guard checks (aggIn "memory(1, unit(16), pointer(32), little, align(4))"
    "memory(1) size(4) align(2) field(0, ptr(1))")
  [fieldAt 0 "has a type aligned to 4 units, more than the layout's 2"]
-- A layout of a nested module is checked against the module's one layout.
#guard checks (oneFunc ("module @dev() {\n  aggregate @s() memory(1) size(4) align(4) {\n  }\n\n}\n"))
  ["the layout describes memory 1, which the data layout does not declare"]

/-! # The units and alignment of a field -/

-- In memory 0, `i24` takes 3 units aligned to 4, so an element of a
-- repeated field takes 4.
example : Core.Ty.fieldShape (DataLayout.entry []) 0 (.int 24) = some (3, 4) := by decide
example : roundUp 3 4 = 4 := by decide
-- A field takes the units and alignment of one value that `alloca` makes.
example : Core.Ty.fieldShape (DataLayout.entry []) 0 (.ptr 0) =
    some (Core.allocaShape (DataLayout.entry []) id (.ptr 0) 1 none 0) :=
  Core.Ty.fieldShape_eq_allocaShape _ _ trivial

/-! # The layouts a run gives each op -/

/-- The placed fields of the layout `@s` that a run of the module of the
text `t` gives each op, if it parses and has one. -/
def placed (t : String) : Option (List (Nat × Nat × Option Nat)) :=
  match parseCore t with
  | .ok m => (m.runItems.layout? "s").map fun l =>
    l.fields.map fun f => (f.offset, f.stride, f.count)
  | .error _ => none

-- Each element of four `i24` in memory 0 starts 4 units after the one
-- before; in a memory of 16-bit units, 2 after.
#guard placed (agg "memory(0) size(16) align(4) field(0, i24, 4)") == some [(0, 4, some 4)]
#guard placed (aggIn mem16 "memory(1) size(4) align(2) field(0, i24, 2)") ==
  some [(0, 2, some 2)]
#guard placed (agg pair) == some [(0, 8, none), (8, 8, none)]
-- A run gives no layout for a symbol that names none, and a nested
-- module's layouts are its own table's, not its parent's.
#guard (match parseCore (agg pair) with
  | .ok m => (m.runItems.layout? "t").isNone
  | .error _ => false)
#guard placed (oneFunc ("module @dev() {\n  aggregate @s() " ++ pair ++ " {\n  }\n\n}\n")) ==
  none

end FirTest
