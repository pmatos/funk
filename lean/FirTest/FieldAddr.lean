import FirTest.Div
import FirTest.PointerOffset
import FirTest.ValidateOps

/-!
Tests of #236's field address `fieldaddr`. Its rule is checked on concrete
layouts in `Fir/Core/FieldAddr.lean`, and its laws are proved; these check
it through validation and through `FirRef.runBytes`, which computes what
`fir-ref run` writes. A field of a struct and an element of an array are
stored through the addresses that `fieldaddr` gives and loaded back, in
memory 0 and in a memory of 16-bit units, so each address is the field's
offset, plus the index times the element's units rounded up to its
alignment: the element 1 of an array of `i24` is 4 units in, not 3 (the
human's ruling of 2026-11-16 on #236, Q2 B). An index out of the field's
elements is an address, as `ptradd` gives one: an access through it is UB
only when it leaves the allocation (Q3 A). A kernel of a nested module
reads its own table's layouts. `crates/funk-ir/tests/field_addr.rs` checks
the same texts, so the two parsers and the two validators agree on each.
-/

namespace FirTest

open Fir FirRef

/-- The layouts of the tests, in memory 0 and in memory 1. -/
def layouts : String :=
  "aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {\n}\n\n" ++
  "aggregate @i24s() memory(0) size(16) align(4) field(0, i24, 4) {\n}\n\n" ++
  "aggregate @wide() memory(1) size(4) align(2) field(0, ptr(1)) field(2, i16, 1) {\n}\n\n"

/-- A module with memory 1 of 16-bit units, the layouts above, and a
function of the body `op` that takes a pointer `%p` of memory `n` and an
index `%k`, and returns the pointer `%q`. -/
def faModule (n : Nat) (op : String) : String :=
  let ptr := if n = 0 then "ptr" else "ptr(" ++ toString n ++ ")"
  memoryOne ++ layouts ++ oneFunc ("func @f(%p: " ++ ptr ++ ", %k: i32) -> " ++ ptr ++
    " {\n^entry:\n  " ++ op ++ "\n  ret %q @0\n}\n")

/-! # The text -/

#guard roundTrips (faModule 0 "%q: ptr = fieldaddr @pair 1 %p @0")
#guard roundTrips (faModule 0 "%q: ptr = fieldaddr @i24s 0 %p, %k @0")
#guard roundTrips (faModule 1 "%q: ptr(1) = fieldaddr @wide 1 %p, %k @0")

/-! # Validation -/

#guard valid (faModule 0 "%q: ptr = fieldaddr @pair 0 %p @0")
#guard valid (faModule 0 "%q: ptr = fieldaddr @pair 1 %p @0")
#guard valid (faModule 0 "%q: ptr = fieldaddr @i24s 0 %p, %k @0")
-- A repeated field named with no index gives its first element.
#guard valid (faModule 0 "%q: ptr = fieldaddr @i24s 0 %p @0")
#guard valid (faModule 1 "%q: ptr(1) = fieldaddr @wide 0 %p @0")
#guard valid (faModule 1 "%q: ptr(1) = fieldaddr @wide 1 %p, %k @0")
-- A symbol that names no layout, a function's included, a field past the
-- layout's, an index on a field that is not repeated, and a layout of
-- another memory than the pointer's.
#guard !valid (faModule 0 "%q: ptr = fieldaddr @none 0 %p @0")
#guard !valid (faModule 0 "%q: ptr = fieldaddr @f 0 %p @0")
#guard !valid (faModule 0 "%q: ptr = fieldaddr @pair 2 %p @0")
#guard !valid (faModule 0 "%q: ptr = fieldaddr @pair 1 %p, %k @0")
#guard !valid (faModule 0 "%q: ptr = fieldaddr @wide 0 %p @0")
#guard !valid (faModule 1 "%q: ptr(1) = fieldaddr @pair 0 %p @0")

/-- A layout of the module, a nested module with a layout of its own and
a kernel that names `inner`, and a function that names `outer`. -/
def nestedFa (outer inner : String) : String :=
  "aggregate @out() memory(0) size(8) align(8) field(0, i64) {\n}\n\n" ++
  "module @dev() {\n  aggregate @in() memory(0) size(4) align(4) field(0, i32) {\n  }\n\n" ++
  "  func @g(%p: ptr) -> ptr {\n  ^entry:\n    %q: ptr = fieldaddr " ++ inner ++
  " 0 %p @0\n    ret %q @0\n  }\n\n}\n\n" ++
  oneFunc ("func @f(%p: ptr) -> ptr {\n^entry:\n  %q: ptr = fieldaddr " ++ outer ++
    " 0 %p @0\n  ret %q @0\n}\n")

-- An op names only the layouts of its own table.
#guard valid (nestedFa "@out" "@in")
#guard !valid (nestedFa "@in" "@in")
#guard !valid (nestedFa "@out" "@out")

/-! # Runs -/

/-- Stores `%a` and `%b` through the addresses of the two `i64` fields of
`@two`, and loads each back through the pointer moved by its offset. -/
def structText : String :=
  "aggregate @two() memory(0) size(16) align(8) field(0, i64) field(8, i64) {\n}\n\n" ++
  oneFunc ("func @f(%a: i64, %b: i64) -> i64, i64 {\n^e:\n" ++
    "  %p: ptr = alloca stack i64 2 @0\n" ++
    "  %f0: ptr = fieldaddr @two 0 %p @0\n  %f1: ptr = fieldaddr @two 1 %p @0\n" ++
    "  store nonatomic %a, %f0 @0\n  store nonatomic %b, %f1 @0\n" ++
    "  %eight: i64 = const 8 @0\n  %q: ptr = ptradd %p, %eight @0\n" ++
    "  %x: i64 = load nonatomic %p @0\n  %y: i64 = load nonatomic %q @0\n  ret %x, %y @0\n}\n")

#guard runText structText "@f" ["7", "-9"] == returns ["7", "-9"]

/-- Stores `%v` as the element `%k` of the four `i24` of `@i24s`, and
loads the byte at offset `o` of the 16 bytes that hold them. -/
def arrayText (o : Int) : String :=
  "aggregate @i24s() memory(0) size(16) align(4) field(0, i24, 4) {\n}\n\n" ++
  oneFunc ("func @f(%v: i24, %k: i8) -> i8 {\n^e:\n" ++
    "  %p: ptr = alloca stack i32 4 @0\n" ++
    "  %e: ptr = fieldaddr @i24s 0 %p, %k @0\n  store nonatomic %v, %e @0\n" ++
    "  %o: i64 = const " ++ toString o ++ " @0\n  %b: ptr = ptradd %p, %o @0\n" ++
    "  %x: i8 = load nonatomic %b @0\n  ret %x @0\n}\n")

-- The element 1 starts 4 units in: its first byte is at offset 4, and the
-- byte at 3, which the elements' units alone would place it at, is still
-- poison. The element 3 starts at 12.
#guard runText (arrayText 4) "@f" ["5", "1"] == returns ["5"]
#guard runText (arrayText 3) "@f" ["5", "1"] == returns ["poison"]
#guard runText (arrayText 12) "@f" ["-1", "3"] == returns ["-1"]
-- The elements 4 and -1 are past each end of the allocation: storing there
-- is UB, but computing the address is not.
#guard runText (arrayText 0) "@f" ["5", "4"] == ubBy "an access out of bounds"
#guard runText (arrayText 0) "@f" ["5", "-1"] == ubBy "an access out of bounds"
#guard valid (arrayText 0)

/-- In memory 1, of 16-bit units, stores `%v` as the element `%k` of the
`i16` field of `@w`, and loads the unit at offset `o`. -/
def wideText (o : Int) : String :=
  memoryOne ++ "aggregate @w() memory(1) size(6) align(2) field(0, ptr(1)) field(2, i16, 4) {\n}\n\n" ++
  oneFunc ("func @f(%v: i16, %k: i32) -> i16 {\n^e:\n" ++
    "  %p: ptr(1) = alloca stack i16 6 @0\n" ++
    "  %e: ptr(1) = fieldaddr @w 1 %p, %k @0\n  store nonatomic %v, %e @0\n" ++
    "  %o: i64 = const " ++ toString o ++ " @0\n  %b: ptr(1) = ptradd %p, %o @0\n" ++
    "  %x: i16 = load nonatomic %b @0\n  ret %x @0\n}\n")

-- A pointer of memory 1 takes two 16-bit units, so the field starts at 2,
-- and each `i16` takes one unit.
#guard valid (wideText 0)
#guard runText (wideText 4) "@f" ["-300", "2"] == returns ["-300"]
#guard runText (wideText 5) "@f" ["-300", "3"] == returns ["-300"]
#guard runText (wideText 3) "@f" ["-300", "2"] == returns ["poison"]

/-- A kernel of a nested module that stores through the field 1 of its own
`@s`, which the module's table also names, with another layout. -/
def nestedRun : String :=
  "aggregate @s() memory(0) size(16) align(8) field(0, i64) field(8, i64) {\n}\n\n" ++
  "module @dev() {\n  aggregate @s() memory(0) size(8) align(4) field(0, i32) field(4, i32) {\n  }\n\n" ++
  "  func @k(%v: i32) -> i32 {\n  ^e:\n    %p: ptr = alloca stack i32 2 @0\n" ++
  "    %f: ptr = fieldaddr @s 1 %p @0\n    store nonatomic %v, %f @0\n" ++
  "    %o: i64 = const 4 @0\n    %q: ptr = ptradd %p, %o @0\n" ++
  "    %x: i32 = load nonatomic %q @0\n    ret %x @0\n  }\n\n}\n\n" ++
  oneFunc "func @f() {\n^e:\n  ret @0\n}\n"

-- The kernel's field 1 is at offset 4, as its own table's `@s` places it,
-- not at the 8 of the module's.
#guard valid nestedRun
#guard runText nestedRun "@dev::@k" ["42"] == returns ["42"]

end FirTest
