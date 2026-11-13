import FirTest.ValidateOps

/-!
Tests of a module's data layout (ADR-2026-11-12-1821): its text, which
reads back and prints as itself; the entries that do not decode, each at
the position of the entry; the rules of a valid layout; and the rule that
the layout declares each memory that a type names, nested modules
included. `crates/funk-ir/tests/layout.rs` checks the same texts, so the two
parsers and the two validators agree on each.
-/

namespace FirTest

open Fir

/-- A module with the layout line `layout l` and the one function `f`. -/
def withLayout (l f : String) : String := "layout " ++ l ++ "\n\n" ++ oneFunc f

/-- A function that takes and returns a pointer of memory 1. -/
def ptr1Func : String := "func @f(%p: ptr(1)) -> ptr(1) {\n^e:\n  ret %p @0\n}\n"

/-- An entry that declares memory 1. -/
def mem1 : String := "memory(1, unit(8), pointer(32), little)"

/-- The problem of a type that names memory `n`, which the layout does not
declare. -/
def undeclared (n : Nat) : String :=
  "a type names memory " ++ toString n ++ ", which the data layout does not declare"

/-! # The text -/

#guard roundTrips (withLayout mem1 ptr1Func)
#guard roundTrips (withLayout ("memory(0, unit(16), pointer(32), little, align(1)), " ++
  "memory(7, unit(8), pointer(64), big, nonintegral), " ++
  "memory(1, unit(8), pointer(32), little, align(2), nonintegral)") ptr1Func)
#guard roundTrips ("dialects toy\n\n" ++ withLayout mem1 ptr1Func)

-- Entries that do not decode, at the position of the entry.
#guard rejectedAt (withLayout "memory(1)" ptr1Func) 1 8 "not an entry of the data layout"
#guard rejectedAt (withLayout "memory(1, unit(8), pointer(32), middle)" ptr1Func) 1 8 "not an entry"
#guard rejectedAt (withLayout "memory(16777216, unit(8), pointer(32), little)" ptr1Func) 1 8
  "not an entry"
#guard rejectedAt (withLayout "memory(-1, unit(8), pointer(32), little)" ptr1Func) 1 8 "not an entry"
#guard rejectedAt (withLayout "memory(1, unit(8), pointer(16777216), little)" ptr1Func) 1 8
  "not an entry"
#guard rejectedAt (withLayout "memory(1, pointer(32), unit(8), little)" ptr1Func) 1 8 "not an entry"
#guard rejectedAt
  (withLayout "memory(1, unit(8), pointer(32), little, nonintegral, align(2))" ptr1Func) 1 8
  "not an entry"
#guard rejectedAt (withLayout "memory(1, unit(8), pointer(32), little, align)" ptr1Func) 1 8
  "not an entry"
#guard rejectedAt (withLayout (mem1 ++ ", mem(2)") ptr1Func) 1 49 "not an entry"
-- A layout with no entry reads the next word as one, and the item's symbol
-- then starts no item.
#guard rejectedAt ("layout\n\n" ++ oneFunc ptr1Func) 3 6 "an item or the location table"
-- The layout follows the dialect set, and a nested module has none.
#guard !accepts ("layout " ++ mem1 ++ "\n\ndialects toy\n\n" ++ oneFunc ptr1Func)
#guard !accepts (oneFunc ("module @dev() {\n  layout " ++ mem1 ++ "\n\n}\n"))

/-! # Validation -/

#guard valid (withLayout mem1 ptr1Func)
#guard checks (oneFunc ptr1Func) [undeclared 1]
#guard checks (withLayout "memory(2, unit(8), pointer(32), little)" ptr1Func) [undeclared 1]
#guard valid (withLayout "memory(0, unit(8), pointer(32), little)"
  "func @f(%p: ptr) {\n^e:\n  ret @0\n}\n")
#guard checks (withLayout "memory(1, unit(8), pointer(32), big)" ptr1Func)
  ["data layout: memory 1 is big-endian: M1 admits only little-endian memories"]
#guard checks (withLayout "memory(1, unit(0), pointer(0), little, align(3))" ptr1Func)
  ["data layout: memory 1 has a unit of 0 bits: a unit has 1 to 16777215 bits",
   "data layout: memory 1 has pointers of 0 bits: a pointer has 1 to 16777215 bits",
   "data layout: memory 1 aligns its pointers to 3 units: " ++
     "an alignment is a power of two no larger than 16777215"]
#guard checks (withLayout (mem1 ++ ", " ++ mem1) ptr1Func)
  ["data layout: memory 1 is declared more than once"]
#guard valid (withLayout "memory(1, unit(16), pointer(16), little, align(1), nonintegral)"
  ptr1Func)

-- A nested module's pointer types name the memories of the module that
-- holds it.
#guard valid (withLayout mem1 "module @dev() {\n  func @g(%p: ptr(1)) {\n  ^e:\n    ret @0\n  }\n\n}\n")
#guard checks (oneFunc "module @dev() {\n  func @g(%p: ptr(1)) {\n  ^e:\n    ret @0\n  }\n\n}\n")
  [undeclared 1]

/-! # The layout's memories -/

example : DataLayout.Declares [] 0 := DataLayout.declares_zero []
example : ¬ DataLayout.Declares [] 1 := by decide
example : DataLayout.Declares [{ mem := 5, unit := 8, pointer := 64, order := .little }] 5 := by
  decide
example : (DataLayout.memory? [] 0) = some MemLayout.default := rfl
example : isPowerOfTwo 16 ∧ !isPowerOfTwo 24 := by decide

end FirTest
