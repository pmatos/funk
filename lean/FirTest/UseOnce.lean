import FirTest.Mixed

/-!
A test-only dialect with a use-once rule. It shows that a dialect's function
rule can state what no rule of one op can: the result of `toy.once` is used
exactly once in its function, by an op of any dialect, or by a branch that
passes it to a block. The rule is the `validFunc` of the use-once dialect,
and the spec's validation check runs it unchanged.

A valid function ends in a core `ret`, so the tests run in the sum of the
core dialect and this dialect. Through its view, the rule sees the core ops
too. The cases are in `tests/dialects/use-once.cases`, and
`crates/funk-ir/tests/use_once.rs` reads the same file, so the two validators
agree on each of them.

It extends the core dialect, under the test dialects' name `toy`
(ADR-2026-10-30-1146), in the spec's sum (ADR-2026-11-09-1543).
-/

namespace FirTest.UseOnce

/-- An op of the use-once dialect, at an integer width. -/
inductive Op where
  | once (w : Nat)
  | sink (w : Nat)
  deriving Repr, DecidableEq

end FirTest.UseOnce

namespace FirTest

open Fir

/-- The use-once dialect: its ops, over the core dialect's types. -/
abbrev UseOnceDialect : Dialect := OverCore UseOnce.Op

namespace UseOnce

instance : DialectSignature UseOnceDialect where
  sig
    | .once _ => []
    | .sink w => [.inl (.int w)]
  returnTypes
    | .once w => [.inl (.int w)]
    | .sink _ => []
  isTerminator _ := false
  succCount _ := 0

/-- The name of an op. -/
def Op.name : Op → String
  | .once _ => "toy.once"
  | .sink _ => "toy.sink"

/-- The op with this name, at these operand and result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Empty)) : Option Op :=
  match as, ts, rs with
  | [], [], [.inl (.int w)] => if n = "toy.once" then some (.once w) else none
  | [], [.inl (.int w)], [] => if n = "toy.sink" then some (.sink w) else none
  | _, _, _ => none

instance : DialectText UseOnceDialect where
  opName := Op.name
  opAttrs _ := []
  decodeOp := Op.decode
  tyAttr := OverCore.tyAttr
  decodeTy := OverCore.decodeTy

variable {host : Dialect}

/-- Every op of a function, at any depth. -/
def ops (f : Func host) : List (Operation host) := f.allBlocks.flatMap (·.body)

/-- The results of the function's `toy.once` ops. -/
def onceValues (v : DialectView UseOnceDialect host) (f : Func host) : List Name :=
  (ops f).flatMap fun o =>
    match v.op o.op with
    | some (.once _) => o.results.map (·.1)
    | _ => []

/-- The use-once rule: each result of a `toy.once` is used exactly once, by
any op of the function. -/
def FuncValid (v : DialectView UseOnceDialect host) (f : Func host) : Prop :=
  ∀ x ∈ onceValues v f, ((ops f).flatMap Operation.uses).count x = 1

instance (v : DialectView UseOnceDialect host) (f : Func host) : Decidable (FuncValid v f) := by
  unfold FuncValid
  infer_instance

instance : DialectValidation UseOnceDialect where
  validTy := OverCore.ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc v _ f := FuncValid v f

instance : DecidableDialectValidation UseOnceDialect where
  decValidTy t := inferInstanceAs (Decidable (OverCore.ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc v _ f := inferInstanceAs (Decidable (FuncValid v f))

end UseOnce

/-- The sum of the core dialect and the use-once dialect. -/
abbrev CoreUseOnce : Dialect := CoreSum UseOnce.Op

namespace UseOnce

/-- One case of the shared file: its verdict, its name and its text. -/
structure Case where
  accept : Bool
  name : String
  text : String

/-- The cases of the shared file. -/
def cases : List Case :=
  ((include_str "../../tests/dialects/use-once.cases").splitOn "=== ").tail.filterMap fun piece =>
    let lines := piece.splitOn "\n"
    match (lines.headD "").splitOn " " with
    | [verdict, name] => some ⟨verdict == "accept", name, "\n".intercalate lines.tail⟩
    | _ => none

/-- The problem that the check reports for a function that breaks the rule. -/
def broken : Problem :=
  { message := "the function breaks a rule of its dialect", func := some "f",
    block := some "entry", op := none, loc := some 1 }

/-- Whether the check gives a case its verdict: no problem, or the one
problem at the first op of the entry block. -/
def Case.holds (c : Case) : Bool :=
  match (Fir.parse c.text : Except ParseError (Module CoreUseOnce)) with
  | .ok m => m.allProblems == if c.accept then [] else [broken]
  | .error _ => false

#guard cases.length == 9
#guard (cases.filter (·.accept)).length == 4
#guard (cases.filter (!·.holds)).map (·.name) == []

end UseOnce

end FirTest
