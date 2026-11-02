import FirTest.Interpreter
import FirTest.ValidateOps

/-!
Tests of the runs of a function: the fuel that calls share
(ADR-2026-11-02-0836), and the axioms of the proofs of fuel monotonicity,
progress and the no-stuck obligation.

No core op calls a function until #20 names the callee of `call`. So the
runs below give `call` a callee with `callsCallee`, a semantics written for
these tests, not fir's, and keep the core dialect's rules for every other
op. They run the spec's interpreter as it is, and show that a call charges
its callee's steps to its caller's budget, so that a run that recurses
without end runs out of fuel. #20 gives `call` its rules and their proofs.
-/

namespace FirTest

open Fir FirRef

/-- A semantics for these tests, not fir's: `call @g` calls `@g`. -/
@[instance_reducible] def callsCallee : DialectCall CoreDialect where
  callee?
    | .call g _ _ => some g
    | _ => none

/-- What `fir-ref run` would report on `@f` of the text `t`, when `call`
calls its callee. -/
def runCalls (t : String) (args : List String) (fuel : Nat) : Option RunReport :=
  match parseCore t with
  | .error _ => none
  | .ok m => (m.funcs.find? (·.name == "f")).bind fun f =>
    match testArgs (f.params.map (·.2)) args with
    | .error _ => none
    | .ok vs => letI := callsCallee
      some (scriptedReport "@f" ((f.run m (m := Tree) vs fuel).run.script constOf [] 0))

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
#guard runCalls (callsInARow 1) ["41"] 5 == some (returns ["42"])
#guard runCalls (callsInARow 1) ["41"] 4 == some exhausted
#guard runCalls (callsInARow 2) ["41"] 9 == some (returns ["43"])
#guard runCalls (callsInARow 2) ["41"] 8 == some exhausted
#guard (List.range 9).all fun n => runCalls (callsInARow 2) ["41"] n == some exhausted
#guard runCalls (callsInARow 2) ["127"] 100 == some (returns ["-127"])

/-! # A run that recurses without end runs out of fuel -/

/-- `@f` calls itself on its argument, and returns what it returns. -/
def recursesForever : String :=
  oneFunc "func @f(%a: i8) -> i8 {\n^e:\n  %r: i8 = call @f %a @0\n  ret %r @0\n}\n"

#guard valid recursesForever
#guard runCalls recursesForever ["1"] 0 == some exhausted
#guard runCalls recursesForever ["1"] 1000 == some exhausted

-- Without a callee, `call` has no rule, as in `fir-ref run`.
#guard runText (callsInARow 1) "@f" ["41"] == fails 2 "fir-ref: @f: call @g has no execution rules yet"

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
