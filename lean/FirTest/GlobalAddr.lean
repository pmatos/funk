import FirTest.Div
import FirTest.PointerOffset
import FirTest.ValidateOps

/-!
Tests of #237's address of a global `globaladdr`. Its rule is checked on
concrete records in `Fir/Core/GlobalAddr.lean`, and its laws are proved;
these check it through validation and through `FirRef.runBytes`, which
computes what `fir-ref run` writes. A run starts with one allocation for
each global of its function's table, so `globaladdr` gives a pointer to
the first unit of one: its initializer reads back, then zeros up to its
size (the human's ruling of 2026-11-20 on #237, Q1); a table of pointers
in an initializer is followed; and a store to a constant global is UB
when it runs (Q2). A function of a nested module names and holds only its
own table's globals (Q3). `crates/funk-ir/tests/global_addr.rs` checks the
same texts, so the two parsers and the two validators agree on each.
-/

namespace FirTest

open Fir FirRef

/-- The globals of the tests, in memory 0 and in memory 1, and a layout
whose symbol is not a global's. -/
def gaGlobals : String :=
  "global @msg() size(8) align(1) const units(104, 105, 0) {\n}\n\n" ++
  "global @wide() memory(1) size(4) align(2) {\n}\n\n" ++
  "aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {\n}\n\n"

/-- A module with memory 1 of 16-bit units, the globals above, and a
function of the body `op` that returns the pointer `%q` of memory `n`. -/
def gaModule (n : Nat) (op : String) : String :=
  let ptr := if n = 0 then "ptr" else "ptr(" ++ toString n ++ ")"
  memoryOne ++ gaGlobals ++ oneFunc ("func @f() -> " ++ ptr ++
    " {\n^entry:\n  " ++ op ++ "\n  ret %q @0\n}\n")

/-! # The text -/

#guard roundTrips (gaModule 0 "%q: ptr = globaladdr @msg @0")
#guard roundTrips (gaModule 1 "%q: ptr(1) = globaladdr @wide @0")
#guard roundTrips (gaModule 0 "%q: ptr = globaladdr @\"a b\" @0")

/-! # Validation -/

#guard valid (gaModule 0 "%q: ptr = globaladdr @msg @0")
#guard valid (gaModule 1 "%q: ptr(1) = globaladdr @wide @0")
-- A symbol that names no global, a function's and a layout's included,
-- and a global of another memory than the result's.
#guard !valid (gaModule 0 "%q: ptr = globaladdr @none @0")
#guard !valid (gaModule 0 "%q: ptr = globaladdr @f @0")
#guard !valid (gaModule 0 "%q: ptr = globaladdr @pair @0")
#guard !valid (gaModule 0 "%q: ptr = globaladdr @wide @0")
#guard !valid (gaModule 1 "%q: ptr(1) = globaladdr @msg @0")

/-- A global of the module, a nested module with a global of its own and a
function that names `inner`, and a function that names `outer`. -/
def nestedGa (outer inner : String) : String :=
  "global @out() size(8) align(8) {\n}\n\n" ++
  "module @dev() {\n  global @in() size(4) align(4) {\n  }\n\n" ++
  "  func @g() -> ptr {\n  ^entry:\n    %q: ptr = globaladdr " ++ inner ++
  " @0\n    ret %q @0\n  }\n\n}\n\n" ++
  oneFunc ("func @f() -> ptr {\n^entry:\n  %q: ptr = globaladdr " ++ outer ++
    " @0\n  ret %q @0\n}\n")

-- An op names only the globals of its own table.
#guard valid (nestedGa "@out" "@in")
#guard !valid (nestedGa "@in" "@in")
#guard !valid (nestedGa "@out" "@out")

/-! # Runs -/

/-- `@msg`, `@table` of pointers into `@msg` and to `@count`, and
`@count`; `@f` loads the pointer at `%i` of `@table` and the unit it
points to, and `@w` stores `%v` through the address of `@msg`. -/
def tableText : String :=
  "global @msg() size(4) align(1) const units(104, 105) {\n}\n\n" ++
  "global @table() size(24) align(8) addr(@msg) addr(@msg, 1) addr(@count) {\n}\n\n" ++
  "global @count() size(1) align(1) units(9) {\n}\n\n" ++
  "func @f(%i: i64) -> i8 {\n^e:\n  %t: ptr = globaladdr @table @0\n" ++
  "  %k: i64 = const 8 @0\n  %o: i64 = mul %i, %k @0\n  %e: ptr = ptradd %t, %o @0\n" ++
  "  %p: ptr = load nonatomic %e @0\n  %v: i8 = load nonatomic %p @0\n  ret %v @0\n}\n\n" ++
  "func @at(%i: i64) -> i8 {\n^e:\n  %m: ptr = globaladdr @msg @0\n" ++
  "  %p: ptr = ptradd %m, %i @0\n  %v: i8 = load nonatomic %p @0\n  ret %v @0\n}\n\n" ++
  oneFunc ("func @w(%v: i8) {\n^e:\n  %m: ptr = globaladdr @msg @0\n" ++
    "  store nonatomic %v, %m @0\n  ret @0\n}\n")

#guard valid tableText
-- The table holds the addresses of `@msg`, of its unit 1 and of `@count`.
#guard runText tableText "@f" ["0"] == returns ["104"]
#guard runText tableText "@f" ["1"] == returns ["105"]
#guard runText tableText "@f" ["2"] == returns ["9"]
-- `@msg`'s units past its initializer are zeros, and one past its size is
-- out of bounds.
#guard runText tableText "@at" ["3"] == returns ["0"]
#guard runText tableText "@at" ["4"] == ubBy "an access out of bounds"
-- Writing a constant global is UB when it runs.
#guard runText tableText "@w" ["1"] == ubBy "a store to a constant allocation"

/-- A nested module whose function reads its own `@g`, which the module's
table also names, with another initializer. -/
def nestedGaRun : String :=
  "global @g() size(1) align(1) units(1) {\n}\n\n" ++
  "module @dev() {\n  global @g() size(1) align(1) units(2) {\n  }\n\n" ++
  "  func @k() -> i8 {\n  ^e:\n    %p: ptr = globaladdr @g @0\n" ++
  "    %v: i8 = load nonatomic %p @0\n    ret %v @0\n  }\n\n}\n\n" ++
  oneFunc ("func @f() -> i8 {\n^e:\n  %p: ptr = globaladdr @g @0\n" ++
    "  %v: i8 = load nonatomic %p @0\n  ret %v @0\n}\n")

-- Each function reads its own table's `@g`.
#guard valid nestedGaRun
#guard runText nestedGaRun "@f" == returns ["1"]
#guard runText nestedGaRun "@dev::@k" == returns ["2"]

end FirTest
