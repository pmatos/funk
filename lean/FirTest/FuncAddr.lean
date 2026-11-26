import FirTest.GlobalStart
import FirTest.PtrInt
import FirTest.PointerOffset

/-!
Tests of #235's address of a function `funcaddr`. Its rule is checked on
concrete records in `Fir/Core/FuncAddr.lean`, and its laws are proved;
these check it through validation, through the memories a run starts
with, and through `FirRef.runBytes`, which computes what `fir-ref run`
writes. A function's address is an allocation of the kind `function`, one
for each function of the run's own table, in memory 0, after the table's
globals of memory 0, with no units, made when the run starts and live for
the whole run (the human's ruling of 2026-11-19 on #235, Q1). So a load or
a store through it is UB, exposing two functions' addresses gives two
different integers, and a table of function pointers stored in memory
loads back. `crates/funk-ir/tests/func_addr.rs` checks the same texts, so
the two parsers and the two validators agree on each.
-/

namespace FirTest

open Fir FirRef Memory

/-- A module whose function `@f` returns the pointer `%q` of memory `n`
that `op` defines, beside a global `@msg`, a layout `@pair` and an
external declaration `@ext`, with memory 1 of 16-bit units. -/
def fnModule (n : Nat) (op : String) : String :=
  let ptr := if n = 0 then "ptr" else "ptr(" ++ toString n ++ ")"
  memoryOne ++ "global @msg() size(1) align(1) {\n}\n\n" ++
    "aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {\n}\n\n" ++
    "extern @ext() {\n}\n\n" ++ oneFunc ("func @f() -> " ++ ptr ++
    " {\n^entry:\n  " ++ op ++ "\n  ret %q @0\n}\n")

/-! # The text -/

#guard roundTrips (fnModule 0 "%q: ptr = funcaddr @f @0")
#guard roundTrips (fnModule 0 "%q: ptr = funcaddr @\"a b\" @0")
-- A result of another memory decodes; validation rejects it.
#guard roundTrips (fnModule 1 "%q: ptr(1) = funcaddr @f @0")

/-! # Validation -/

#guard valid (fnModule 0 "%q: ptr = funcaddr @f @0")
-- A symbol that names no function: none, a global's, a layout's and an
-- external declaration's; and a result of memory 1.
#guard !valid (fnModule 0 "%q: ptr = funcaddr @none @0")
#guard !valid (fnModule 0 "%q: ptr = funcaddr @msg @0")
#guard !valid (fnModule 0 "%q: ptr = funcaddr @pair @0")
#guard !valid (fnModule 0 "%q: ptr = funcaddr @ext @0")
#guard !valid (fnModule 1 "%q: ptr(1) = funcaddr @f @0")

/-- A function `@out` of the module, a nested module with a function `@in`
and a function `@g` that names `inner`, and a function `@f` that names
`outer`. -/
def nestedFn (outer inner : String) : String :=
  "func @out() {\n^e:\n  ret @0\n}\n\n" ++
  "module @dev() {\n  func @in() {\n  ^e:\n    ret @0\n  }\n\n" ++
  "  func @g() -> ptr {\n  ^e:\n    %q: ptr = funcaddr " ++ inner ++
  " @0\n    ret %q @0\n  }\n\n}\n\n" ++
  oneFunc ("func @f() -> ptr {\n^e:\n  %q: ptr = funcaddr " ++ outer ++ " @0\n  ret %q @0\n}\n")

-- An op names only the functions of its own table.
#guard valid (nestedFn "@out" "@in")
#guard !valid (nestedFn "@in" "@in")
#guard !valid (nestedFn "@out" "@out")

/-! # The memories a run starts with -/

/-- Two globals of memory 0, one of memory 1, and the functions `@f` and
`@g`. -/
def fnStart : String :=
  memoryOne ++ "global @a() size(1) align(1) {\n}\n\nglobal @b() memory(1) size(1) align(1) {\n}\n\n" ++
    "global @c() size(2) align(2) {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n\n" ++
    oneFunc "func @g() {\n^e:\n  ret @0\n}\n"

-- In memory 0 the functions follow the globals, each a constant block of
-- kind `function` with no units, aligned to 1. Memory 1 holds its global
-- only.
#guard startBlocks fnStart 0 0 == some [(.global, 1, false, ["0"]), (.global, 2, false, ["0", "0"]),
  (.function, 1, true, []), (.function, 1, true, [])]
#guard startBlocks fnStart 0 1 == some [(.global, 1, false, ["0"])]
-- A run of a nested module's function holds its own table's functions only.
#guard startBlocks (nestedFn "@out" "@in") 0 0 ==
  some [(.function, 1, true, []), (.function, 1, true, [])]
#guard startBlocks (nestedFn "@out" "@in") 1 0 ==
  some [(.function, 1, true, []), (.function, 1, true, [])]
-- A store to a function's block faults, as it has no unit.
#guard storeAt fnStart 0 2 == "an access out of bounds"

/-! # Runs -/

/-- `@f` and `@g`; `@addr` returns both addresses, `@load` loads a unit
through `@f`'s, `@store` stores one there, `@moved` loads through it moved
by `%i`, `@exposed` exposes both and returns their difference, and
`@table` stores both into a table of two pointers and loads the one at
`%i` back. -/
def fnRuns : String :=
  "func @f() {\n^e:\n  ret @0\n}\n\nfunc @g() {\n^e:\n  ret @0\n}\n\n" ++
  "func @addr() -> ptr, ptr {\n^e:\n  %a: ptr = funcaddr @f @0\n  %b: ptr = funcaddr @g @0\n" ++
  "  ret %a, %b @0\n}\n\n" ++
  "func @load() -> i8 {\n^e:\n  %a: ptr = funcaddr @f @0\n  %v: i8 = load nonatomic %a @0\n" ++
  "  ret %v @0\n}\n\n" ++
  "func @store(%v: i8) {\n^e:\n  %a: ptr = funcaddr @f @0\n  store nonatomic %v, %a @0\n" ++
  "  ret @0\n}\n\n" ++
  "func @moved(%i: i64) -> i8 {\n^e:\n  %a: ptr = funcaddr @f @0\n  %p: ptr = ptradd %a, %i @0\n" ++
  "  %v: i8 = load nonatomic %p @0\n  ret %v @0\n}\n\n" ++
  "func @exposed() -> i64 {\n^e:\n  %a: ptr = funcaddr @f @0\n  %b: ptr = funcaddr @g @0\n" ++
  "  %x: i64 = ptr_expose %a @0\n  %y: i64 = ptr_expose %b @0\n  %d: i64 = sub %y, %x @0\n" ++
  "  ret %d @0\n}\n\n" ++
  oneFunc ("func @table(%i: i64) -> ptr {\n^e:\n  %t: ptr = alloca stack ptr 2 @0\n" ++
    "  %a: ptr = funcaddr @f @0\n  %b: ptr = funcaddr @g @0\n  store nonatomic %a, %t @0\n" ++
    "  %k: i64 = const 8 @0\n  %t1: ptr = ptradd %t, %k @0\n  store nonatomic %b, %t1 @0\n" ++
    "  %o: i64 = mul %i, %k @0\n  %e: ptr = ptradd %t, %o @0\n  %p: ptr = load nonatomic %e @0\n" ++
    "  ret %p @0\n}\n")

#guard valid fnRuns
-- The table's functions are memory 0's allocations 0 to 7, in its order.
#guard runText fnRuns "@addr" == returns ["ptr(0, 0)", "ptr(1, 0)"]
-- A function's allocation has no units: every access through it is out of
-- bounds, moved or not (Q1).
#guard runText fnRuns "@load" == ubBy "an access out of bounds"
#guard runText fnRuns "@store" ["1"] == ubBy "an access out of bounds"
#guard runText fnRuns "@moved" ["0"] == ubBy "an access out of bounds"
#guard runText fnRuns "@moved" ["-1"] == ubBy "an access out of bounds"
-- Exposed, each function takes an address of its own: the canonical layout
-- puts `@g` two addresses after `@f`.
#guard runText fnRuns "@exposed" == returns ["2"]
-- A table of function pointers in memory loads back: the stack table is
-- the allocation after the functions'.
#guard runText fnRuns "@table" ["0"] == returns ["ptr(0, 0)"]
#guard runText fnRuns "@table" ["1"] == returns ["ptr(1, 0)"]

end FirTest
