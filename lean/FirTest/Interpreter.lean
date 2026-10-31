import FirTest.Run

/-!
Tests of the interpreter's paths that the core ops with rules do not reach.
`const`, `add`, `sub`, `mul`, the bitwise ops and shifts, the width changes,
`freeze` and `ret` are never UB, and none of them jumps. So two semantics
written here for these tests, not fir's, give the interpreter what #18 and
#19 will: `addIsUB`, in which `add` is UB, and `brJumps`, in which `br`
goes to its successor. Every other op keeps the core dialect's rules. The
runs are those of `fir-ref run`, in the tree of choices, and are reported
as it reports them, in scripted mode with no choices. Functions built
here, not parsed, reach the stuck cases that no text that decodes can
reach.
-/

namespace FirTest

open Fir FirRef

/-- The tree of choices that `fir-ref run` runs the core dialect in. -/
abbrev Tree := ChoiceTree Core.Op

/-- A semantics, not fir's, in which `add` is UB. -/
@[instance_reducible] def addIsUB : DialectDenote CoreDialect Tree where
  denote
    | .add .., _ => MonadUB.ub "add is \"UB\"\nhere"
    | op, args => DialectDenote.denote (m := Tree) op args
  exit := DialectDenote.exit (m := Tree)

/-- A semantics, not fir's, in which `br` goes to its one successor. -/
@[instance_reducible] def brJumps : DialectDenote CoreDialect Tree where
  denote := DialectDenote.denote (m := Tree)
  exit
    | .br, _ => pure (.goto 0)
    | op, args => DialectDenote.exit (m := Tree) op args

/-- An argument of type `t` for these tests: `poison`, which `fir-ref run`
does not take, or an argument that it reads. -/
def testArg : (t : Core.Ty) → String → Except String ⟦t⟧
  | .int w, "poison" => pure (.poison : PoisonOr (BitVec w))
  | t, s => readArg t s

/-- One test argument for each type of `ts`. -/
def testArgs : (ts : List Core.Ty) → List String → Except String (HVector toType ts)
  | [], [] => pure .nil
  | t :: ts, a :: as => return .cons (← testArg t a) (← testArgs ts as)
  | _, _ => .error "a number of arguments other than the parameters"

/-- What `fir-ref run` would report on the function `f` with the semantics
`s`, on arguments that may be `poison`. -/
def runFuncIn (s : DialectDenote CoreDialect Tree) (f : Func CoreDialect)
    (args : List String := []) (fuel : Nat := defaultFuel) : Option RunReport :=
  match testArgs (f.params.map (·.2)) args with
  | .error _ => none
  | .ok vs => letI := s
    some (scriptedReport "@f" ((f.run (m := Tree) vs fuel).run.script constOf [] 0))

/-- What `fir-ref run` would report on the first function of the text `t`
with the semantics `s`. -/
def runIn (s : DialectDenote CoreDialect Tree) (t : String) (args : List String := [])
    (fuel : Nat := defaultFuel) : Option RunReport :=
  match parseCore t with
  | .error _ => none
  | .ok m => m.funcs.head?.bind (runFuncIn s · args fuel)

/-! # UB

An op's UB ends its path: what follows does not run. Its reason is escaped
in the JSON. -/

/-- The report of a run that hits UB because `add` is UB. -/
def addUB : RunReport :=
  { out := "{\"kind\":\"ub\",\"reason\":\"add is \\\"UB\\\"\\nhere\",\"choices\":0}", status := 0 }

#guard runIn addIsUB (addAt "i8") ["1", "2"] == some addUB
#guard runIn addIsUB (addAt "i8") ["poison", "2"] (fuel := 1) == some addUB
#guard runIn addIsUB (addAt "i8") ["1", "2"] (fuel := 0) ==
  some exhausted
#guard runIn addIsUB (body "func @f(%a: i8) -> i8"
    ["^e:", "  %s: i8 = add %a, %a @0", "  %t: i8 = sub %s, %s @0", "  ret %t @0"]) ["1"] ==
  some addUB
-- Without the test's semantics, `add` gives a sum.
#guard runIn inferInstance (addAt "i8") ["1", "2"] == some (returns ["3"])

/-! # Jumps

A jump binds the target block's arguments to the values that the successor
passes, and runs the target. -/

#guard runIn brJumps (body "func @f(%a: i8) -> i8"
    ["^e:", "  br ^n(%a) @0", "^n(%x: i8):", "  %y: i8 = add %x, %x @0", "  ret %y @0"]) ["5"] ==
  some (returns ["10"])
-- A value defined before a jump is defined after it.
#guard runIn brJumps (body "func @f(%a: i8) -> i8, i8"
    ["^e:", "  %c: i8 = const 2 @0", "  br ^n @0", "^n:", "  ret %c, %a @0"]) ["poison"] ==
  some (returns ["2", "poison"])
-- A loop runs until its fuel is exhausted. Each op takes a step: the run
-- below runs three.
#guard runIn brJumps (body "func @f(%a: i8) -> i8"
    ["^e:", "  br ^l(%a) @0", "^l(%i: i8):", "  %j: i8 = add %i, %i @0", "  br ^l(%j) @0"])
    ["1"] (fuel := 1000) == some exhausted
#guard runIn brJumps (body "func @f() -> i8"
    ["^e:", "  %c: i8 = const 1 @0", "  br ^n @0", "^n:", "  ret %c @0"]) (fuel := 2) ==
  some exhausted
#guard runIn brJumps (body "func @f() -> i8"
    ["^e:", "  %c: i8 = const 1 @0", "  br ^n @0", "^n:", "  ret %c @0"]) (fuel := 3) ==
  some (returns ["1"])

/-! # Stuck on a jump -/

#guard runIn brJumps (body "func @f()" ["^e:", "  br @0"]) == some (stuckBy "the terminator has no successor 0")
#guard runIn brJumps (body "func @f()" ["^e:", "  br ^nope @0"]) ==
  some (stuckBy "^nope is not a block of the function")
#guard runIn brJumps (body "func @f(%a: i8)" ["^e:", "  br ^n @0", "^n(%x: i8):", "  ret @0"]) ["1"] ==
  some (stuckBy "^n takes a number of arguments other than its successor passes")
-- A block argument of another type is stuck at the jump, whether or not
-- the block uses it.
#guard runIn brJumps (body "func @f(%a: i8) -> i16"
    ["^e:", "  br ^n(%a) @0", "^n(%x: i16):", "  ret %x @0"]) ["1"] ==
  some (stuckBy "^n takes arguments of types other than its successor passes")
#guard runIn brJumps (body "func @f(%a: i8)" ["^e:", "  br ^n(%a) @0", "^n(%x: i16):", "  ret @0"])
    ["1"] == some (stuckBy "^n takes arguments of types other than its successor passes")
#guard runIn brJumps (body "func @f() -> i8"
    ["^e:", "  br ^n(%y) @0", "^n(%x: i8):", "  %y: i8 = const 1 @0", "  ret %x @0"]) ==
  some (stuckBy "%y is not defined")

/-! # Stuck on an op that no text reaches

`Core.Op.decode` builds each op instance from its operand and result types
in text, so a text that decodes always gives an op as many operands and
results as it takes, of its types. A function built here need not. -/

/-- `@f(%a: t) -> i8`, whose one block runs `o`, then `ret %s`. -/
def withOp (t : Core.Ty) (o : Operation CoreDialect) : Func CoreDialect :=
  ⟨"f", [("a", t)], [.int 8], ⟨[⟨"e", [], [o, ⟨[], .ret [.int 8], ["s"], [], [], 0⟩]⟩]⟩⟩

#guard runFuncIn inferInstance (withOp (.int 8) ⟨[("s", .int 8)], .add 8 {}, ["a", "a"], [], [], 0⟩)
    ["1"] == some (returns ["2"])
#guard runFuncIn inferInstance (withOp (.int 8) ⟨[("s", .int 8)], .add 8 {}, ["a"], [], [], 0⟩)
    ["1"] == some (stuckBy "an op has a number of operands other than its op instance takes")
#guard runFuncIn inferInstance
    (withOp (.int 8) ⟨[("s", .int 8), ("t", .int 8)], .add 8 {}, ["a", "a"], [], [], 0⟩) ["1"] ==
  some (stuckBy "an op names a number of results other than it gives")
#guard runFuncIn inferInstance (withOp (.int 16) ⟨[("s", .int 8)], .add 8 {}, ["a", "a"], [], [], 0⟩)
    ["1"] == some (stuckBy "%a does not have the operand's type")

/-! # The obligations' axioms

The obligations of `const`, `add` (with any flags) and `ret` rest on
`propext` and `Quot.sound`, two of Lean's standard axioms
(ADR-2026-10-30-1452). The semantics of every core op is one definition,
and Lean's `&&&`, `|||` and `^^^` on `BitVec N`, which the bitwise ops use,
rest on `Quot.sound`, so every core obligation does too. -/

/-- info: 'Fir.Core.add_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.add_propagatesPoison

/-- info: 'Fir.Core.add_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.add_returnsOnDefined

/-- info: 'Fir.Core.add_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.add_total

/-- info: 'Fir.Core.add_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.add_monotone

/-- info: 'Fir.Core.const_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.const_returnsOnDefined

/-- info: 'Fir.Core.const_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.const_total

/-- info: 'Fir.Core.ret_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ret_total

/-- info: 'Fir.Core.ret_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ret_monotone

end FirTest
