import FirTest.Div
import FirTest.Compare
import FirTest.ValidateOps

/-!
Tests of #19's ops on `FirRef.runBytes`, which computes what `fir-ref run`
writes: where `br` and `cond_br` go, at `i1`, `i7`, `i8`, `i33`, `i64`,
`i128` and the widest type; a branch on poison, which is immediate UB with
its reason and ends the run; a poison block argument, which arrives as
poison; a branch on a frozen poison, which may go either way; and the
forbidden rewrite of a `select` into a `cond_br` on the same condition.
`fir-ref run` takes no `poison` argument, so the tests of poison operands
run the same rules through `runIn`, and others make poison with a broken
flag. `FirTest.Loops` tests loops. Every function that these tests run is
valid, so its runs mean something (ADR-2026-10-30-1856), but for one, whose
successor ends without a terminator: UB ends its run first.
-/

namespace FirTest

open Fir FirRef

/-! # Where `cond_br` goes -/

/-- `@f(%c: i1, %a: T, %b: T) -> T`, which goes to `^x(%a)` when `%c` is
`true` and to `^y(%b)` when it is `false`, and returns what it passed. -/
def condBrAt (ty : String) : String :=
  body ("func @f(%c: i1, %a: " ++ ty ++ ", %b: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  cond_br %c, ^x(%a), ^y(%b) @0", "^x(%p: " ++ ty ++ "):", "  ret %p @0",
     "^y(%q: " ++ ty ++ "):", "  ret %q @0"]

#guard selectWidths.all fun (ty, _, _) => valid (condBrAt ty)
-- `true` goes to the first successor and `false` to the second, each with
-- the values it passes.
#guard selectWidths.all fun (ty, a, b) =>
  runText (condBrAt ty) "@f" ["true", a, b] == returns [a] &&
    runText (condBrAt ty) "@f" ["false", a, b] == returns [b]

/-- `@f(%a: i8, %b: i8) -> i8`, whose `br` goes to a block with no
arguments, which uses values that the entry block defines. -/
def brOn : String :=
  body "func @f(%a: i8, %b: i8) -> i8"
    ["^e:", "  %s: i8 = sub %a, %b @0", "  br ^n @0", "^n:", "  %t: i8 = add %s, %a @0",
     "  ret %t @0"]

#guard valid brOn
#guard runText brOn "@f" ["7", "2"] == returns ["12"]

/-! # A branch on poison is UB

A poison condition is immediate UB, with the reason `cond_br on poison`. It
ends the run: no successor runs, whatever the successors pass. -/

#guard selectWidths.all fun (ty, a, b) =>
  runIn inferInstance (condBrAt ty) ["poison", a, b] == some (ubBy "cond_br on poison") &&
    runIn inferInstance (condBrAt ty) ["poison", "poison", "poison"] ==
      some (ubBy "cond_br on poison")

/-- `@f(%a: i1) -> i8`, which branches on `add nsw %a, %a`: `false` when
`%a` is `false`, and poison when it is `true`, since `-1 + -1` overflows
`i1`. Each successor returns a value of its own. -/
def onOverflow : String :=
  body "func @f(%a: i1) -> i8"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  cond_br %p, ^x, ^y @0", "^x:",
     "  %one: i8 = const 1 @0", "  ret %one @0", "^y:", "  %two: i8 = const 2 @0", "  ret %two @0"]

#guard valid onOverflow
#guard runText onOverflow "@f" ["false"] == returns ["2"]
#guard runText onOverflow "@f" ["true"] == ubBy "cond_br on poison"
#guard explore onOverflow ["true"] ==
  outcomes ["{\"kind\":\"ub\",\"reason\":\"cond_br on poison\"}"] 0
#guard runText onOverflow "@f" ["true"] (mode := .sampled 3) ==
  { out := "{\"kind\":\"ub\",\"reason\":\"cond_br on poison\",\"choices\":0,\"sequence\":[]}",
    status := 0 }
-- UB ends the path: the successor, which would be stuck, does not run.
#guard runText (body "func @f(%a: i1) -> i8"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  cond_br %p, ^x, ^x @0", "^x:",
     "  %one: i8 = const 1 @0"]) "@f" ["true"] == ubBy "cond_br on poison"
-- It takes its step of fuel first.
#guard runText onOverflow "@f" ["true"] (fuel := 1) == exhausted
#guard runText onOverflow "@f" ["true"] (fuel := 2) == ubBy "cond_br on poison"

/-! # A poison block argument arrives as poison

`br` and `cond_br` pass their successors' values on as they are. A poison
that reaches a block argument stays poison there: returning it returns
poison, and branching on it is UB. -/

/-- `@f(%a: T) -> T`, which passes `%a` to `^n` and returns it. -/
def passAt (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  br ^n(%a) @0", "^n(%x: " ++ ty ++ "):", "  ret %x @0"]

#guard selectWidths.all fun (ty, a, _) =>
  valid (passAt ty) &&
    runIn inferInstance (passAt ty) ["poison"] == some (returns ["poison"]) &&
    runText (passAt ty) "@f" [a] == returns [a]
-- Each successor of `cond_br` passes poison on too, and the poison that a
-- broken flag gives arrives as poison.
#guard selectWidths.all fun (ty, a, b) =>
  runIn inferInstance (condBrAt ty) ["true", "poison", b] == some (returns ["poison"]) &&
    runIn inferInstance (condBrAt ty) ["false", a, "poison"] == some (returns ["poison"]) &&
    runIn inferInstance (condBrAt ty) ["true", a, "poison"] == some (returns [a])

/-- `@f(%a: i8, %c: i1) -> i8, i8`, which passes `add nsw %a, %a` and `%a`
to `^n`, from either successor of `cond_br`. -/
def passOverflow : String :=
  body "func @f(%a: i8, %c: i1) -> i8, i8"
    ["^e:", "  %p: i8 = add nsw %a, %a @0", "  cond_br %c, ^n(%p, %a), ^n(%a, %p) @0",
     "^n(%x: i8, %y: i8):", "  ret %x, %y @0"]

#guard valid passOverflow
#guard runText passOverflow "@f" ["100", "true"] == returns ["poison", "100"]
#guard runText passOverflow "@f" ["100", "false"] == returns ["100", "poison"]
#guard runText passOverflow "@f" ["10", "true"] == returns ["20", "10"]

/-- `@f(%a: i1) -> i8`, which passes `add nsw %a, %a` to `^n`, which
branches on it. -/
def branchOnArg : String :=
  body "func @f(%a: i1) -> i8"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  br ^n(%p) @0", "^n(%x: i1):",
     "  %one: i8 = const 1 @0", "  cond_br %x, ^y(%one), ^y(%one) @0", "^y(%r: i8):",
     "  ret %r @0"]

#guard valid branchOnArg
#guard runText branchOnArg "@f" ["false"] == returns ["1"]
#guard runText branchOnArg "@f" ["true"] == ubBy "cond_br on poison"

/-! # A branch on a frozen poison

`freeze` gives a value that is not poison, so `cond_br` on it is not UB:
the run may go to either successor, one for each value of the choice. -/

/-- `onOverflow`, with its condition frozen. -/
def onFrozen : String :=
  body "func @f(%a: i1) -> i8"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0", "  cond_br %f, ^x, ^y @0",
     "^x:", "  %one: i8 = const 1 @0", "  ret %one @0", "^y:", "  %two: i8 = const 2 @0",
     "  ret %two @0"]

#guard valid onFrozen
#guard explore onFrozen ["true"] == outcomes [ret ["2"], ret ["1"]] 1
#guard runText onFrozen "@f" ["true"] (mode := .scripted ["true"]) == returns ["1"] 1
#guard runText onFrozen "@f" ["true"] (mode := .scripted ["false"]) == returns ["2"] 1
#guard explore onFrozen ["false"] == outcomes [ret ["2"]] 0

/-! # A `select` becomes a `cond_br` only with its condition frozen

Where `%c` may be poison, a `cond_br` on `%c` whose successors pass the
values of `select %c, %x, %y` to one block is not a sound rewrite of the
`select`. When `%c` is poison, the `select` gives poison, and the
`cond_br` is UB. A source that returns allows only returns that refine
it, and UB is not one, so the rewrite's outcome is not allowed by the
`select`'s. `cond_br` on `%f = freeze %c` is sound: it returns `%x` or
`%y`, and poison allows every value. `%c` is `add nsw %a, %b` at `i1`, as
in `FirTest.Compare`: `false` when `%a` and `%b` are both `false`, `true`
when exactly one is `true`, and poison when both are. The tests run all
four. -/

/-- `@f(%a: i1, %b: i1, %x: i8, %y: i8) -> i8`, which runs `lines` on
`%c = add nsw %a, %b`. -/
def branched (lines : List String) : String :=
  body "func @f(%a: i1, %b: i1, %x: i8, %y: i8) -> i8"
    (["^e:", "  %c: i1 = add nsw %a, %b @0"] ++ lines)

/-- The source: `select %c, %x, %y`. -/
def selectSource : String := branched ["  %s: i8 = select %c, %x, %y @0", "  ret %s @0"]

/-- The wrong rewrite: `cond_br %c`, to one block that takes the value. -/
def condBrForm : String :=
  branched ["  cond_br %c, ^j(%x), ^j(%y) @0", "^j(%s: i8):", "  ret %s @0"]

/-- The sound rewrite: `cond_br %f`, with `%f = freeze %c`. -/
def frozenCondBrForm : String :=
  branched ["  %f: i1 = freeze %c @0", "  cond_br %f, ^j(%x), ^j(%y) @0", "^j(%s: i8):",
    "  ret %s @0"]

#guard [selectSource, condBrForm, frozenCondBrForm].all valid
-- Where `%c` is poison, the `select` gives poison and the `cond_br` is UB:
-- the rewrite is wrong. On `freeze %c`, it returns `%x` or `%y`, each of
-- which the `select`'s poison allows.
#guard explore selectSource ["true", "true", "5", "7"] == outcomes [ret ["poison"]] 0
#guard explore condBrForm ["true", "true", "5", "7"] ==
  outcomes ["{\"kind\":\"ub\",\"reason\":\"cond_br on poison\"}"] 0
#guard explore frozenCondBrForm ["true", "true", "5", "7"] == outcomes [ret ["7"], ret ["5"]] 1
-- Where `%c` is not poison, all three give the value it chooses.
#guard [(["false", "false"], "7"), (["true", "false"], "5"), (["false", "true"], "5")].all
  fun (ab, v) => [selectSource, condBrForm, frozenCondBrForm].all fun t =>
    explore t (ab ++ ["5", "7"]) == outcomes [ret [v]] 0
-- The outcomes above, as the spec's refinement of outcomes reads them.
example : ¬ ((.ret [⟨.int 8, .poison⟩] : Outcome Core.Obs) ⊑
    (.ub "cond_br on poison" : Outcome Core.Obs)) := id
example : (.ret [⟨.int 8, .poison⟩] : Outcome Core.Obs) ⊑
    (.ret [⟨.int 8, .value 5⟩] : Outcome Core.Obs) :=
  Core.poison_isRefinedBy 8 _

/-! # The obligations' axioms -/

/-- info: 'Fir.Core.br_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.br_total

/-- info: 'Fir.Core.br_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.br_monotone

/-- info: 'Fir.Core.br_goto_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.br_goto_lt

/-- info: 'Fir.Core.condBr_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.condBr_total

/-- info: 'Fir.Core.condBr_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.condBr_monotone

/-- info: 'Fir.Core.condBr_goto_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.condBr_goto_lt

end FirTest
