import FirTest.Interpreter
import FirTest.Sum
import FirTest.Toy

/-!
A module that mixes core ops and a toy op, in the sum of the core dialect
and the toy dialect, `CoreToy`. The sum sends each op name that starts with
`toy.` to the toy dialect and every other name to the core dialect: the rule
for test dialects, ADR-2026-10-30-2040. No core op name starts with `toy.`
and the toy op's does, so the sum's text is lawful.

The tests run the spec's parser, printer, validation check and interpreter
on such a module, unchanged: it parses, prints as itself, is valid, and runs
with the toy op's rule. A toy op that breaks its own rule is rejected by
validation, and the core dialect alone does not read the toy op.
-/

namespace FirTest

open Fir FirRef

/-- A test dialect's op name: `toy.` and the rest of the name. -/
def isToyName (n : String) : Bool := "toy.".toList.isPrefixOf n.toList

instance : SumRoute Core.Op Toy.Op := ⟨isToyName⟩

/-- The sum of the core dialect and the toy dialect. -/
abbrev CoreToy : Dialect := SumDialect Core.Ty Core.Op Toy.Op

/-- No core op name starts with `toy.`, and the toy op's does. -/
theorem coreToy_routes : SumDialect.Routes Core.Ty Core.Op Toy.Op := by
  refine ⟨fun o => ?_, fun o => ?_⟩
  · cases o <;> simp only [opName, Core.Op.name] <;> decide
  · cases o; exact (by decide : isToyName "toy.mask" = true)

instance : LawfulDialectText CoreToy := SumDialect.lawful coreToy_routes

/-- Every valid module of the sum is well formed, as the spec proves of
every dialect with lawful text. -/
theorem coreToy_validIsWellFormed : ValidIsWellFormed (d := CoreToy) := validIsWellFormed

#guard isToyName "toy.mask" && isToyName "toy." && !isToyName "toy" && !isToyName "add"
-- A name that starts with `toy.` goes to the toy dialect, whether or not it
-- decodes there, and every other name to the core dialect.
#guard decodeOp (d := CoreToy) "toy.mask" [.int 3] [.int 8] [.int 8] == some (.inr (.mask 8 3))
#guard decodeOp (d := CoreToy) "toy.add" [] [.int 8, .int 8] [.int 8] == none
#guard decodeOp (d := CoreToy) "add" [] [.int 8, .int 8] [.int 8] == some (.inl (.add 8 {}))
-- Each op of the sum has its own dialect's poison class.
#guard Core.samples.all (fun o => poisonClass (d := CoreToy) (.inl o) == Core.Op.poisonClass o) &&
  poisonClass (d := CoreToy) (.inr (.mask 8 3)) == .propagates

/-! # Running a mixed module

The spec's semantics of the sum is the set monad's: each side's instance,
lifted. The tests run the same rules in `Mix`, a tree of choices whose
paths with no outcome name the op without a rule, as `fir-ref run` runs
the core dialect's, and walk it in scripted mode with no choices. -/

example (f : Func CoreToy) (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    Run (List (DVal CoreToy)) :=
  f.run (m := SetM) args fuel

/-- The tree of choices that the tests run a mixed module in. A path with
no outcome names the op that has no rule for what the interpreter asks of
it. -/
abbrev Mix := ChoiceTree String

/-- The core dialect's rules, in `Mix`. -/
instance : DialectDenote CoreDialect Mix where
  denote op args := match op.denote? (m := Mix) with
    | some rule => rule args
    | none => .noOutcome op.name
  exit op args := match op.exit? (m := Mix) with
    | some rule => rule args
    | none => .noOutcome op.name

/-- The toy dialect's rule, in `Mix`. A toy op is not a terminator, so it
has no exit. -/
instance : DialectDenote ToyDialect Mix where
  denote := Toy.Op.denote
  exit op _ := .noOutcome op.name

/-- Parses with the sum of the core and the toy dialect. -/
def parseMixed (t : String) : Except ParseError (Module CoreToy) := Fir.parse t

/-- What `fir-ref run` would report on the first function of the text `t`,
in the sum, on arguments that may be `poison`. -/
def runMixed (t : String) (args : List String := []) (fuel : Nat := defaultFuel) :
    Option RunReport :=
  match parseMixed t with
  | .error _ => none
  | .ok m => m.funcs.head?.bind fun f =>
    match testArgs (f.params.map (·.2)) args with
    | .error _ => none
    | .ok vs => some <| match (f.run (m := Mix) vs fuel).run.script constOf [] 0 with
      | .ok (.ok r, c) => scriptedReport "@f" (.ok (.ok r, c))
      | .ok (.ub r, c) => scriptedReport "@f" (.ok (.ub r, c))
      | .ok (.noOutcome op, _) => { err := s!"{op} has no rule", status := 2 }
      | .error _ => { err := "the run makes a choice", status := 2 }

/-- `@f(%a: T) -> T, T` that masks `%a` to its low `k` bits, then adds
`%a` to the mask: a toy op whose result a core op uses. -/
def maskAdd (ty k : String) : String :=
  "func @f(%a: " ++ ty ++ ") -> " ++ ty ++ ", " ++ ty ++ " {\n^entry:\n  %m: " ++ ty ++
    " = toy.mask " ++ k ++ " %a @1\n  %s: " ++ ty ++ " = add %m, %a @0\n  ret %m, %s @0\n}\n\n" ++
    "locs {\n  @0 = unknown\n  @1 = name(\"mask\")\n}\n"

/-- The mixed module of these tests. -/
def mixed : String := maskAdd "i8" "3"

/-! # Parsing and printing -/

-- The sum reads the module, and prints it as itself.
#guard match parseMixed mixed with
  | .ok m => m.print == mixed
  | .error _ => false
-- The core dialect alone does not read the toy op.
#guard rejectedAt mixed 3 12 "op toy.mask does not decode"
-- A text of core ops alone reads the same in the sum.
#guard match parseMixed seven with
  | .ok m => m.print == seven
  | .error _ => false
-- A toy op that does not decode is a parse error, at its name.
#guard match parseMixed (maskAdd "i8" "-1") with
  | .error e => e.pos == ⟨3, 12⟩ && (e.reason.splitOn "op toy.mask does not decode").length > 1
  | .ok _ => false
#guard (parseMixed (mixed.replace "%m: i8 = toy.mask 3 %a" "%m: i16 = toy.mask 3 %a")).toBool ==
  false

/-! # Validation -/

/-- The problems that the validation check finds in the text `t`, in the
sum, if it parses. -/
def mixedProblems (t : String) : Option (List Problem) :=
  match parseMixed t with
  | .ok m => some m.problems
  | .error _ => none

#guard mixedProblems mixed == some []
#guard mixedProblems (maskAdd "i8" "8") == some [] && mixedProblems (maskAdd "i8" "0") == some []
-- `toy.mask 9` at `i8` decodes, and breaks the toy dialect's own rule.
#guard mixedProblems (maskAdd "i8" "9") ==
  some [{ message := "the op breaks its dialect's own rule", func := some "f",
          block := some "entry", op := some 0, loc := some 1 }]
#guard mixedProblems (maskAdd "i1" "2") ==
  some [{ message := "the op breaks its dialect's own rule", func := some "f",
          block := some "entry", op := some 0, loc := some 1 }]
-- The core dialect's rules hold in the sum too: `ret` returns the function's
-- result types, and `call` names a function of the module.
#guard mixedProblems (mixed.replace ") -> i8, i8 {" ") -> i8 {") ==
  some [{ message := "the op breaks its dialect's own rule", func := some "f",
          block := some "entry", op := some 2, loc := some 0 }]
#guard mixedProblems (mixed.replace "add %m, %a" "call @g %m") ==
  some [{ message := "the op refers to @g, which names no function", func := some "f",
          block := some "entry", op := some 1, loc := some 0 },
        { message := "the op breaks its dialect's own rule", func := some "f",
          block := some "entry", op := some 1, loc := some 0 }]
#guard mixedProblems (mixed.replace "add %m, %a" "call @f %m" |>.replace ") -> i8, i8 {" ") -> i8 {"
    |>.replace "ret %m, %s" "ret %s") == some []

/-! # Running -/

-- 13 is 0b1101: its low three bits are 5, and 5 + 13 is 18.
#guard runMixed mixed ["13"] == some (returns ["5", "18"])
#guard runMixed mixed ["-1"] == some (returns ["7", "6"])
#guard runMixed mixed ["poison"] == some (returns ["poison", "poison"])
#guard runMixed (maskAdd "i8" "0") ["-1"] == some (returns ["0", "-1"])
#guard runMixed (maskAdd "i8" "8") ["-128"] == some (returns ["-128", "0"])
#guard runMixed (maskAdd "i1" "1") ["true"] == some (returns ["true", "false"])
#guard runMixed (maskAdd "i16777215" "1") ["-1"] == some (returns ["1", "0"])
-- Each op takes a step of fuel, the toy op included.
#guard runMixed mixed ["13"] (fuel := 2) == some exhausted
#guard runMixed mixed ["13"] (fuel := 3) == some (returns ["5", "18"])

/-! # The theorems' axioms -/

/-- info: 'FirTest.SumDialect.lawful_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SumDialect.lawful_iff

/-- info: 'FirTest.SumDialect.names_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SumDialect.names_disjoint

/-- info: 'FirTest.SumDialect.lawfulPoison' does not depend on any axioms -/
#guard_msgs in #print axioms SumDialect.lawfulPoison

/-- info: 'FirTest.Toy.lawfulDialectText' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Toy.lawfulDialectText

/-- info: 'FirTest.coreToy_routes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreToy_routes

/-- info: 'FirTest.coreToy_validIsWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreToy_validIsWellFormed

end FirTest
