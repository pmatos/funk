import FirTest.Validate

/-!
Tests of the check of a location table at 1,000,000 entries, and of a fused
location of 1,000,000 references (#136). Through `FirTest.Validate`, this
module imports `FirRef.Fast`, as `fir-ref` does, so `LocTable.problems` runs
as `FirRef.locTableProblems`, which takes no stack per entry or reference.
Most checks have errors at the start, in the middle and at the end: a
reference out of order, a repeated one, a location that refers to itself,
to an entry after it or to one that the table does not hold, and a number
of `2^32` or more. The checks run on the table alone, through
`Module.problems`, through `decide`, and through `FirRef.reportModule`,
what `fir-ref validate` runs once a text parses. The last check pins the
axioms of the theorem to Lean's standard ones.

These checks test the answers at this size, not the stack. The spec's
check recurses in core's compiled code, whose frames are small, and the
elaborator's stack is large: the spec's check passes them too, and aborts
only when `lean` runs with a `--tstack` of 65,536 KiB or less on the
entries, or of 16,384 KiB or less on the references
(ADR-2026-11-05-0745). The stack is tested by running `fir-ref validate`
with `LEAN_STACK_SIZE_KB=256`.
-/

namespace FirTest

open Fir

/-- The messages of the problems of a location table. -/
def tableMessages (t : LocTable) : List String := t.problems.map (·.message)

/-- The entries `@0` to `@(n - 1)`, each `unknown`. -/
def unknowns (n : Nat) : LocTable := (List.range n).map fun i => (i, .unknown)

/-- `n` references, to `@0` and `@1` in turn. -/
def alternating (n : Nat) : List LocRef := (List.range n).map (· % 2)

/-- The entries `@0 = unknown`, `@1 = unknown`, and `@2`, which fuses `refs`. -/
def fusedOf (refs : List LocRef) : LocTable := [(0, .unknown), (1, .unknown), (2, .fused refs)]

/-- The entries `@0` to `@(n - 1)`, with errors at the start, in the middle
and at the end, for `n` of 8 or more: `@1` comes first, and `@0`
refers to itself; `@(n / 2 + 1)` is `@(n / 2)` again, and the first
`@(n / 2)` refers to it; `@(n - 1)` fuses `@(n - 2)` with `@n`, which the
table does not hold; and the table ends with `@4294967296`. -/
def flawed (n : Nat) : LocTable :=
  (1, .unknown) :: (List.range n).map (fun i =>
    if i = 0 then (0, .derived 0)
    else if i = n / 2 then (i, .callsite (i - 1) (i + 1))
    else if i = n / 2 + 1 then (n / 2, .unknown)
    else if i = n - 1 then (i, .fused [i - 1, n])
    else (i, .unknown)) ++ [(4294967296, .unknown)]

/-- What the check finds in `flawed n`. -/
def flawedMessages (n : Nat) : List String :=
  ["location table: @0 comes after @1: references are unique and in increasing order",
   s!"location table: @{n / 2} comes after @{n / 2}: references are unique and in increasing order",
   "location table: @0 refers to @0, which does not come before it",
   s!"location table: @{n / 2} refers to @{n / 2 + 1}, which the table does not hold",
   s!"location table: @{n - 1} refers to @{n}, which the table does not hold",
   "location table: @4294967296 holds a reference, line or column of 2^32 or more"]

/-- `@2` fuses `n` references with errors at the start, in the middle and at
the end: to `@3`, which the table does not hold, to `@2` itself, and to
`@4294967296`. -/
def flawedRefs (n : Nat) : List LocRef :=
  3 :: alternating n ++ 2 :: alternating n ++ [4294967296]

/-- What the check finds in `fusedOf (flawedRefs n)`. -/
def flawedRefsMessages : List String :=
  ["location table: @2 holds a reference, line or column of 2^32 or more",
   "location table: @2 refers to @3, which the table does not hold",
   "location table: @2 refers to @2, which does not come before it",
   "location table: @2 refers to @4294967296, which the table does not hold"]

/-- What `fir-ref validate` reports on the file `t.fir` once it parses as a
module with no items and a valid table. -/
def acceptedReport : String × UInt32 :=
  ("{\"file\":\"t.fir\",\"verdict\":\"accepted\",\"diagnostics\":[]}", 0)

/-- What `fir-ref validate` reports on the file `t.fir` once it parses as a
module with no items and a table whose only problem is `message`. -/
def rejectedReport (message : String) : String × UInt32 :=
  ("{\"file\":\"t.fir\",\"verdict\":\"validation-error\",\"diagnostics\":[{\"kind\":" ++
    "\"validation-error\",\"message\":\"" ++ message ++ "\",\"func\":null,\"block\":null," ++
    "\"op\":null,\"loc\":null}]}", 1)

/-! # Small tables -/

#guard tableMessages (flawed 8) == flawedMessages 8
#guard tableMessages (fusedOf (flawedRefs 3)) == flawedRefsMessages
#guard tableMessages (unknowns 6) == [] && tableMessages (fusedOf (alternating 6)) == []

/-! # A million entries, and a million references -/

#guard tableMessages (unknowns 1000000) == []
#guard tableMessages (flawed 1000000) == flawedMessages 1000000
#guard tableMessages (fusedOf (alternating 1000000)) == []
#guard tableMessages (fusedOf (flawedRefs 500000)) == flawedRefsMessages

#guard messages (moduleOf [] (flawed 1000000)) == flawedMessages 1000000
#guard decideValid (moduleOf [] (unknowns 1000000))
#guard !decideValid (moduleOf [] (fusedOf (flawedRefs 500000)))

#guard FirRef.reportModule "t.fir" (moduleOf [] (unknowns 1000000)) == acceptedReport
#guard FirRef.reportModule "t.fir" (moduleOf [] (fusedOf (alternating 1000000))) == acceptedReport
#guard FirRef.reportModule "t.fir" (moduleOf [] (unknowns 999999 ++ [(999999, .fused [0, 1000000])]))
  == rejectedReport "location table: @999999 refers to @1000000, which the table does not hold"

/-! # The axioms of the proof -/

/--
info: 'FirRef.problems_eq_locTableProblems' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.problems_eq_locTableProblems

end FirTest
