import FirTest.Mixed

/-!
A region kind whose ops are unordered (ADR-2026-11-10-1941), on the shared
cases of `tests/dialects/region-kinds.cases`. `crates/funk-ir/tests/region_kind_cases.rs`
reads them too, so `funk verify` and `fir-ref`'s check agree on each case,
and both print each case as itself, so it round-trips byte for byte across
Rust and Lean.

A test dialect named `toy` has two ops: `toy.graph`, which takes and gives
nothing and owns one region of the kind `toy.dataflow`, and `toy.node`,
which takes any number of values of one type `iN` and gives one of that
type. The kind's rule has its own scoping and its own terminators: the
region holds one block with no arguments; every op of the block is an op
of `toy`, none of which is a terminator, so no op ends the block; and each
value an op of the block uses is a result of an op of the same block,
before or after it, or a parameter of the function. The rule sees the
host's ops through the dialect's view, so it is written once and holds in
any sum.

The tests read the cases with the spec's parser, print them with its
printer and check them with its validation check, which `fir-ref` runs
through its `@[csimp]` copies. The dialect's text is lawful, so the spec's
round-trip theorems hold for every module of the sum of the core and the
dialect. The interpreter runs `toy.graph` by the dialect's semantics and
does not enter its region.
-/

namespace FirTest.Dataflow

/-- An op of the dataflow dialect: `graph`, and `node w n`, which takes `n`
values of type `iN` with `N = w`. -/
inductive Op where
  | graph
  | node (w n : Nat)
  deriving Repr, DecidableEq

end FirTest.Dataflow

namespace FirTest

open Fir FirRef

/-- The dataflow dialect over the core. -/
abbrev DataflowDialect : Dialect := OverCore Dataflow.Op

/-- The sum of the core and the dataflow dialect. -/
abbrev CoreDataflow : Dialect := CoreSum Dataflow.Op

namespace Dataflow

/-- The operand types of an op. -/
def Op.sig : Op → List (Core.Ty ⊕ Empty)
  | .graph => []
  | .node w n => List.replicate n (.inl (.int w))

/-- The result types of an op. -/
def Op.returnTypes : Op → List (Core.Ty ⊕ Empty)
  | .graph => []
  | .node w _ => [.inl (.int w)]

instance : DialectSignature DataflowDialect where
  sig := Op.sig
  returnTypes := Op.returnTypes
  isTerminator _ := false
  succCount _ := 0
  regionKinds
    | .graph => ["toy.dataflow"]
    | .node .. => []

/-- The name of an op. -/
def Op.name : Op → String
  | .graph => "toy.graph"
  | .node .. => "toy.node"

/-- The op with this name, with no attributes, at these operand and result
types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Empty)) : Option Op :=
  match as, rs with
  | [], [] => if n = "toy.graph" ∧ ts = [] then some .graph else none
  | [], [.inl (.int w)] =>
    if n = "toy.node" ∧ ts.all (decide <| · = .inl (.int w)) then some (.node w ts.length)
    else none
  | _, _ => none

instance : DialectText DataflowDialect where
  opName := Op.name
  opAttrs _ := []
  decodeOp := Op.decode
  tyAttr := OverCore.tyAttr
  decodeTy := OverCore.decodeTy

/-- The rule of the kind `toy.dataflow`: the region holds one block with no
arguments, every op of the block is the dialect's, and each value an op of
the block uses is a result of an op of the block, in any order, or a
parameter of the function. -/
def dataflow {host : Dialect} (v : DialectView DataflowDialect host) (f : Func host)
    (r : Region host) : Bool :=
  match r.blocks with
  | [b] =>
    let defs := (b.body.flatMap (·.results)).map (·.1) ++ f.params.map (·.1)
    b.params.isEmpty && b.body.all (fun o => (v.op o.op).isSome) &&
      b.body.all fun o => o.operands.all defs.contains
  | _ => false

instance : DialectValidation DataflowDialect where
  validTy := OverCore.ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True
  regionKindNames := ["toy.dataflow"]
  validRegion v k _ f r := k = "toy.dataflow" ∧ dataflow v f r = true

instance : DecidableDialectValidation DataflowDialect where
  decValidTy t := inferInstanceAs (Decidable (OverCore.ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)
  decValidRegion v k _ f r :=
    inferInstanceAs (Decidable (k = "toy.dataflow" ∧ dataflow v f r = true))

instance : DialectCall DataflowDialect := ⟨fun _ => none⟩

/-- The rule of each op: `toy.graph` gives nothing and `toy.node` gives
zero. -/
def Op.denote {m : Type → Type} [Monad m] : (op : Op) →
    HVector toType (Fir.sig (d := DataflowDialect) op) →
    m (HVector toType (Fir.returnTypes (d := DataflowDialect) op))
  | .graph, _ => pure .nil
  | .node .., _ => pure (.cons (.value 0) .nil)

/-- The dialect's semantics. No op of the dialect is a terminator, so none
has an exit. -/
instance : DialectDenote DataflowDialect Mix where
  denote := Op.denote
  exit op _ := .noOutcome op.name

/-! # The dialect's text is lawful -/

/-- Every op decodes from its name, at its operand and result types. -/
theorem Op.decode_encode (o : Op) : Op.decode o.name [] o.sig o.returnTypes = some o := by
  cases o <;> simp [Op.decode, Op.name, Op.sig, Op.returnTypes]

/-- An op decodes only from its own name, at its own operand and result
types, with no attributes. -/
theorem Op.encode_decode {n : String} {as : List Attr} {ts rs : List (Core.Ty ⊕ Empty)} {o : Op}
    (h : Op.decode n as ts rs = some o) : o.name = n ∧ [] = as ∧ o.sig = ts ∧ o.returnTypes = rs := by
  unfold Op.decode at h
  split at h
  · split at h
    · rename_i hn
      cases h
      exact ⟨hn.1.symm, rfl, hn.2.symm, rfl⟩
    · cases h
  · split at h
    · rename_i w hn
      cases h
      refine ⟨hn.1.symm, rfl, ?_, rfl⟩
      exact (List.eq_replicate_iff.mpr
        ⟨rfl, fun t ht => by simpa using List.all_eq_true.mp hn.2 t ht⟩).symm
    · cases h
  · cases h

instance : LawfulDialectText DataflowDialect where
  decodeOp_encode := Op.decode_encode
  encode_decodeOp _ _ _ _ _ h := Op.encode_decode h
  decodeTy_encode := OverCore.decodeTy_attr
  encode_decodeTy _ _ h := OverCore.attr_decodeTy h
  opName_isWord
    | .graph => (by decide : isWord "toy.graph")
    | .node .. => (by decide : isWord "toy.node")
  opAttrs_writable _ := trivial
  tyAttr_isType := OverCore.attr_isType

/-- The dialect writes its ops and its kind under its name. -/
instance : LawfulDialectName CoreDialect (Ext Op) where
  opName_named
    | .graph => (by decide : wordDialect "toy.graph" = some "toy")
    | .node .. => (by decide : wordDialect "toy.node" = some "toy")
  opAttrs_mem _ _ h := nomatch h
  tyAttr_named t := t.elim
  tyAttr_mem t := t.elim
  kind_named k hk := by
    simp only [regionKindNames, List.mem_singleton] at hk
    subst hk
    decide

/-- The dataflow dialect's name is new to the core. -/
theorem dataflow_new : name (Ext Op) ∉ names CoreDialect := Core.name_new _

instance : LawfulDialectText CoreDataflow := Dialect.sum.lawful_of_names dataflow_new

/-- `parse(print(m)) == m` for every well-formed module of the sum of the
core and the dataflow dialect, regions of the kind `toy.dataflow` included. -/
theorem printThenParse : PrintThenParse (d := CoreDataflow) Fir.parse :=
  Dialect.sum.printThenParse dataflow_new

/-- `print(parse(t)) == t` for every text printed from a well-formed module
of the sum. -/
theorem parseThenPrint : ParseThenPrint (d := CoreDataflow) Fir.parse := Fir.parseThenPrint

/-- Every valid module of the sum is well formed. -/
theorem validIsWellFormed : ValidIsWellFormed (d := CoreDataflow) :=
  Dialect.sum.validIsWellFormed dataflow_new

/-- info: 'FirTest.Dataflow.printThenParse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printThenParse

/-- The sum sends a region of the kind `toy.dataflow` to the dialect's rule. -/
example {host : Dialect} (v : DialectView CoreDataflow host) (ctx : FuncContext host)
    (f : Func host) (r : Region host) :
    validRegion v "toy.dataflow" ctx f r ↔
      "toy.dataflow" = "toy.dataflow" ∧ dataflow (Dialect.sum.extView v) f r = true :=
  Dialect.sum.validRegion_ext dataflow_new v (List.mem_singleton_self _) ctx f r

/-! # The shared cases -/

/-- What a case expects: no problem, a problem of the general rules and none
of the kind's rule, or a problem of the kind's rule. -/
inductive Verdict where
  | accept
  | reject
  | rejectByKind
  deriving BEq

/-- One case of the shared file: its verdict, its name and its text. -/
structure Case where
  verdict : Verdict
  name : String
  text : String

/-- The verdict that a word of a case's first line names. -/
def Verdict.read : String → Option Verdict
  | "accept" => some .accept
  | "reject" => some .reject
  | "reject-by-kind" => some .rejectByKind
  | _ => none

/-- The cases of the shared file. -/
def cases : List Case :=
  ((include_str "../../tests/dialects/region-kinds.cases").splitOn "=== ").tail.filterMap fun piece =>
    let lines := piece.splitOn "\n"
    match (lines.headD "").splitOn " " with
    | [v, name] => (Verdict.read v).map fun v => ⟨v, name, "\n".intercalate lines.tail⟩
    | _ => none

/-- The problem that the check reports for a region that breaks the rule of
its kind. -/
def breaks : String := "a region of the op breaks the rule of its kind toy.dataflow"

/-- The messages of the problems of a text, and of its dialect set, in the
sum, or the parse error's reason. -/
def messages (t : String) : List String :=
  match (Fir.parse t : Except ParseError (Module CoreDataflow)) with
  | .ok m => m.allProblems.map (·.message)
  | .error e => ["parse: " ++ e.reason]

/-- Whether a case parses, prints as itself, and gets its verdict. -/
def Case.holds (c : Case) : Bool :=
  match (Fir.parse c.text : Except ParseError (Module CoreDataflow)) with
  | .error _ => false
  | .ok m =>
    let ms := m.allProblems.map (·.message)
    m.print == c.text && match c.verdict with
      | .accept => ms.isEmpty
      | .reject => !ms.isEmpty && !ms.contains breaks
      | .rejectByKind => ms.contains breaks

/-- The text of the case with this name. -/
def caseText (name : String) : String := ((cases.find? (·.name == name)).map (·.text)).getD ""

#guard cases.length == 15
#guard (cases.filter (·.verdict == .accept)).length == 4
#guard (cases.filter (·.verdict == .rejectByKind)).length == 7
#guard (cases.filter (!·.holds)).map (·.name) == []

-- A region that breaks the kind's rule is the only problem of these cases.
#guard ["two-blocks", "a-block-argument", "a-core-op-inside", "a-terminator-inside",
  "a-use-of-a-value-of-the-body", "a-use-of-another-graphs-node",
  "a-use-of-the-outer-graphs-node"].all fun n => messages (caseText n) == [breaks]

-- A value defined in a region is not in scope in the function's body, and
-- the two validators say so in the same words.
#guard messages (caseText "a-use-of-a-node-in-the-body") ==
  ["%a is defined inside a region, and is not in scope here"]

/-! # Running

The interpreter runs `toy.graph` by the dialect's semantics, and does not
enter its region. -/

/-- How the run of the first function of a text ends: `ret` with the number
of values it returns, `stuck` with the reason, or `none` when the text does
not parse or the run makes a choice. -/
def runEnd (t : String) : Option String :=
  match (Fir.parse t : Except ParseError (Module CoreDataflow)) with
  | .error _ => none
  | .ok m => m.funcs.head?.bind fun f =>
    match readSumArgs (f.params.map (·.2)) [] with
    | .error _ => none
    | .ok vs =>
      match (f.run m (m := Mix) vs 10).run.script constOf [] 0 with
      | .ok (.ok (.ok (.ret vs)), _) => some s!"ret {vs.length}"
      | .ok (.ok (.ok .fuelExhausted), _) => some "fuel"
      | .ok (.ok (.error e), _) => some ("stuck: " ++ e.reason)
      | _ => none

#guard runEnd (caseText "a-node-of-no-operands") == some "ret 0"

end Dataflow

end FirTest
