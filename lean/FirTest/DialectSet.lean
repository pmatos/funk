import FirTest.SumTypes

/-!
The dialect set of a module (ADR-2026-11-09-1543, ADR-2026-11-10-1306),
on the shared cases of `tests/dialects/dialect-set.cases`, and the dialect
sets of nested modules (ADR-2026-11-10-1510), on those of
`tests/dialects/nested-modules.cases`. `crates/funk-ir/tests/dialect_set.rs`
reads both too, so the two validators agree on each of them.

The cases run in the sum of the core and a test dialect named `toy`: the
flag dialect's type `toy.flag` and its ops `toy.flag` and `toy.test`, and
`toy.note`, which takes any attributes and gives nothing, so an attribute
can name a dialect. A module may write a word of `toy` only when its
dialect set names `toy`. The tagged dialect also registers two kinds of
item, `toy.cell` and `toy.alias` (ADR-2026-11-10-2224), which
`FirTest.ItemKinds` checks.
-/

namespace FirTest.Tagged

open Fir

/-- An op of the tagged dialect: the flag dialect's two, and `note`, which
takes any attributes. -/
inductive Op where
  | make (w : Nat)
  | test
  | note (as : List Attr)

end FirTest.Tagged

namespace FirTest

open Fir

/-- The tagged dialect, before it is put over a base: its ops, and the flag
dialect's type. -/
abbrev TagExt : Dialect := ⟨Tagged.Op, Flag.Ty⟩

instance : DialectName TagExt := ⟨"toy"⟩

/-- The tagged dialect over the core. -/
abbrev TagDialect : Dialect := CoreDialect.over TagExt

/-- The sum of the core dialect and the tagged dialect. -/
abbrev CoreTag : Dialect := CoreDialect ⊞ TagExt

namespace Tagged

instance : DialectSignature TagDialect where
  sig
    | .make w => [.inl (.int w)]
    | .test => [.inr .flag]
    | .note _ => []
  returnTypes
    | .make _ => [.inr .flag]
    | .test => [.inl (.int 1)]
    | .note _ => []
  isTerminator _ := false
  succCount _ := 0

/-- The name of a tagged op. -/
def Op.name : Op → String
  | .make _ => "toy.flag"
  | .test => "toy.test"
  | .note _ => "toy.note"

/-- The tagged op with this name, at these operand and result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Flag.Ty)) : Option Op :=
  if n = "toy.note" then
    match ts, rs with
    | [], [] => some (.note as)
    | _, _ => none
  else (Flag.Op.decode n as ts rs).map fun
    | .make w => .make w
    | .test => .test

instance : DialectText TagDialect where
  opName := Op.name
  opAttrs
    | .note as => as
    | _ => []
  decodeOp := Op.decode
  tyAttr := Flag.tyAttr
  decodeTy := Flag.decodeTy

/-- The tagged dialect's rule for its kinds of item. A `toy.cell` holds a
flag: it has no parameters, its one result is `toy.flag`, which it sees
through its view of the host, and its one attribute is 0 or 1. A
`toy.alias` has no parameters or results, and its one attribute is a symbol
that names a function of its table. -/
def itemRule {host : Dialect} (v : DialectView TagDialect host) (ctx : FuncContext host)
    (i : DialectItem host) : Bool :=
  if i.kind = "toy.cell" then
    i.params.isEmpty && decide (i.results.map v.ty = [some (.inr .flag)]) &&
      match i.attrs with
      | [.int 0] | [.int 1] => true
      | _ => false
  else if i.kind = "toy.alias" then
    i.params.isEmpty && i.results.isEmpty &&
      match i.attrs with
      | [.sym s] => (ctx.symbols s).isSome
      | _ => false
  else false

instance : DialectValidation TagDialect where
  validTy := Flag.ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True
  itemKindNames := ["toy.cell", "toy.alias"]
  validItem v ctx i := itemRule v ctx i = true

instance : DecidableDialectValidation TagDialect where
  decValidTy t := inferInstanceAs (Decidable (Flag.ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)
  decValidItem v ctx i := inferInstanceAs (Decidable (itemRule v ctx i = true))

end Tagged

-- The sum's dialect set is the tagged dialect's name.
#guard names CoreTag == ["toy"]

namespace DialectSetCases

/-- One case of the shared file: its verdict, its name and its text. -/
structure Case where
  accept : Bool
  name : String
  text : String

/-- The cases of a shared file. -/
def read (file : String) : List Case :=
  (file.splitOn "=== ").tail.filterMap fun piece =>
    let lines := piece.splitOn "\n"
    match (lines.headD "").splitOn " " with
    | [verdict, name] => some ⟨verdict == "accept", name, "\n".intercalate lines.tail⟩
    | _ => none

/-- The cases of the shared file on a module's dialect set. -/
def cases : List Case := read (include_str "../../tests/dialects/dialect-set.cases")

/-- The cases of the shared file on the dialect sets of nested modules. -/
def nested : List Case := read (include_str "../../tests/dialects/nested-modules.cases")

/-- Whether the check gives a case its verdict: it parses, prints as itself,
and has no problem exactly when the case is accepted. -/
def Case.holds (c : Case) : Bool :=
  match (Fir.parse c.text : Except ParseError (Module CoreTag)) with
  | .ok m => m.print == c.text && (m.allProblems.isEmpty == c.accept)
  | .error _ => false

#guard cases.length == 13
#guard (cases.filter (·.accept)).length == 6
#guard (cases.filter (!·.holds)).map (·.name) == []
#guard nested.length == 8
#guard (nested.filter (·.accept)).length == 3
#guard (nested.filter (!·.holds)).map (·.name) == []

/-- The problems of the dialect set alone, of a case's text. -/
def setProblems (name : String) : List Problem :=
  match (cases ++ nested).find? (·.name == name) with
  | some c =>
    match (Fir.parse c.text : Except ParseError (Module CoreTag)) with
    | .ok m => m.setProblems
    | .error _ => []
  | none => []

-- A word outside the set is a problem of the function that writes it, and
-- names the first such dialect.
#guard setProblems "op-outside-the-set" ==
  [{ message := "the function writes a word of the dialect toy, " ++
      "which the module's dialect set does not name", func := some "f" }]
#guard setProblems "attribute-outside-the-set" ==
  [{ message := "the function writes a word of the dialect gpu, " ++
      "which the module's dialect set does not name", func := some "f" }]
#guard setProblems "nested-does-not-inherit-the-set" ==
  [{ message := "the function writes a word of the dialect toy, " ++
      "which the module's dialect set does not name", func := some "f" }]
#guard setProblems "unknown-dialect" ==
  [{ message := "the dialect set names gpu, which is not a known dialect" }]

end DialectSetCases

end FirTest
