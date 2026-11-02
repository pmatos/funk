import FirTest.Interpreter
import FirTest.ValidateOps

/-!
Tests of the runs of a function: the fuel that calls share
(ADR-2026-11-02-0836), and the axioms of the proofs of fuel monotonicity,
progress and the no-stuck obligation.

`call @g` calls `@g` (#20). The runs below show that a call charges its
callee's steps to its caller's budget, so that a run that recurses without
end runs out of fuel. Until #20, these tests gave `call` its callee with a
semantics of their own; they now run `fir-ref run`'s, the spec's.
`FirTest.Calls` tests calls further.
-/

namespace FirTest

open Fir FirRef

/-- `@g` adds one to its argument, in three steps, and `@f` calls it
`n` times in a row, then returns the last result. -/
def callsInARow (n : Nat) : String :=
  oneFunc ("func @g(%a: i8) -> i8 {\n^e:\n  %one: i8 = const 1 @0\n" ++
    "  %s: i8 = add %a, %one @0\n  ret %s @0\n}\n\nfunc @f(%a: i8) -> i8 {\n^e:\n" ++
    String.join ((List.range n).map fun k =>
      s!"  %r{k + 1}: i8 = call @g %r{k} @0\n") ++ s!"  ret %r{n} @0\n}\n")
    |>.replace "%r0" "%a"

/-! # A callee's steps are its caller's

One call takes a step, its callee three, and `@f`'s `ret` one: five steps.
Two calls take nine. With a step less, the run runs out of fuel. -/

#guard valid (callsInARow 1) && valid (callsInARow 2)
#guard runText (callsInARow 1) "@f" ["41"] (fuel := 5) == returns ["42"]
#guard runText (callsInARow 1) "@f" ["41"] (fuel := 4) == exhausted
#guard runText (callsInARow 2) "@f" ["41"] (fuel := 9) == returns ["43"]
#guard runText (callsInARow 2) "@f" ["41"] (fuel := 8) == exhausted
#guard (List.range 9).all fun n => runText (callsInARow 2) "@f" ["41"] (fuel := n) == exhausted
#guard runText (callsInARow 2) "@f" ["127"] (fuel := 100) == returns ["-127"]

/-! # A run that recurses without end runs out of fuel -/

/-- `@f` calls itself on its argument, and returns what it returns. -/
def recursesForever : String :=
  oneFunc "func @f(%a: i8) -> i8 {\n^e:\n  %r: i8 = call @f %a @0\n  ret %r @0\n}\n"

#guard valid recursesForever
#guard runText recursesForever "@f" ["1"] (fuel := 0) == exhausted
#guard runText recursesForever "@f" ["1"] (fuel := 1000) == exhausted

/-! # Axioms

The runs of every function are fuel-monotone; the runs of every valid
function of the tracer subset have progress and no stuck path. -/

/-- info: 'Fir.Func.fuelMonotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.fuelMonotone

/-- info: 'Fir.Func.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.progress

/-- info: 'Fir.Func.neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.neverStuck

/-- info: 'Fir.Core.tracer_fuelMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.tracer_fuelMonotone

/-- info: 'Fir.Core.tracer_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.tracer_progress

/-- info: 'Fir.Core.tracer_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.tracer_neverStuck

end FirTest
