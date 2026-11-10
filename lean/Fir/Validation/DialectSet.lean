import Fir.Validation.CheckModule
import Fir.Sum.Names

/-!
A module names, in its dialect set, the dialects other than the core whose
words it writes (ADR-2026-11-09-1543). The text writes the set first, as
`dialects toy, gpu`, and a module that names no dialect writes no set and
uses the core alone (ADR-2026-11-10-1306). A valid module names each
dialect of its set once, by a word. The rule of this section says what the
set may name, and that the module's words keep to it:

* each dialect that the set names is a dialect of `d`'s own set, `names d`:
  a module uses only dialects that its dialect holds;
* each word that the module writes names the core or a dialect of its set:
  the name of each op and each word of its attributes, the kind of each
  region of an op, and each word of each type that a function states, at
  any depth.

A module nested in another has a dialect set of its own, not its parent's
(ADR-2026-11-10-1510), so the rule holds for each symbol table of a module:
its own and that of each nested module, each against its own set. A nested
module whose set names no dialect uses the core alone, whatever its parent
names.

So the words of a module of the sum `core ⊞ toy` that names no dialect are
the core's alone, and its first `toy.` word breaks the rule. A word's
dialect is the part before its first `.`, as the section on words and
dialect sets defines it.

The rule reads the words that the module writes, which the dialect's text
gives. So it is stated here, after words and dialect sets, beside the rule
of a valid module and not in it, and the theorems about valid modules, such
as the round trip and the semantics, need no text of their dialect. A tool
checks both: it reports the problems of `Module.problems` and then those of
`Module.setProblems`.

This section gives the dialects that a function's words name, the rule,
its check, and the proof that the check decides the rule.
-/

namespace Fir

variable {d : Dialect} [DialectText d]

/-- The dialects that the words of an op instance name, in order: its
name's, then those of its attributes. -/
def opDialects (op : d.Op) : List String :=
  (wordDialect (opName op)).toList ++ Attr.dialectsAll (opAttrs op)

/-- The dialects that the words of an op name, in order: those of its op
instance, then the dialect of the kind of each of its regions. -/
def Operation.wordDialects (o : Operation d) : List String :=
  opDialects o.op ++ o.regions.flatMap fun r => (r.kind.bind wordDialect).toList

/-- The dialects that the words of a function name, in order: those of each
type that it states, then those of each of its ops, at any depth. -/
def Func.wordDialects (f : Func d) : List String :=
  f.types.flatMap (fun t => (tyAttr t).dialects) ++
    f.allBlocks.flatMap fun b => b.body.flatMap Operation.wordDialects

variable [DialectSet d]

/-- A symbol table keeps to its dialect set: the set names only dialects of
`d`'s set, and every word of the table's functions names the core or a
dialect of its set. -/
structure SymbolTable.InDialectSet (t : SymbolTable d) : Prop where
  known : ∀ x ∈ t.dialects, x ∈ names d
  words : ∀ f ∈ t.funcs, ∀ x ∈ f.wordDialects, x ∈ t.dialects

/-- A module keeps to its dialect sets: each of its symbol tables, its own
and that of each nested module, keeps to its own set. -/
def Module.InDialectSet (m : Module d) : Prop := ∀ t ∈ m.tables, t.InDialectSet

/-- The problem of a function that writes a word of a dialect that its
table's set does not name: the first such dialect, if there is one. -/
def Func.setProblems (ns : List Name) (f : Func d) : List Problem :=
  match f.wordDialects.find? (· ∉ ns) with
  | some x => [f.problem ("the function writes a word of the dialect " ++ x ++
      ", which the module's dialect set does not name")]
  | none => []

/-- The problems of a symbol table's dialect set: each dialect that it names
and `d` does not hold, then each function that writes a word outside it. -/
def SymbolTable.setProblems (t : SymbolTable d) : List Problem :=
  t.dialects.filterMap (fun x => if x ∈ names d then none else
    some { message := "the dialect set names " ++ x ++ ", which is not a known dialect" }) ++
  t.funcs.flatMap (Func.setProblems t.dialects)

/-- The problems of a module's dialect sets: those of each of its symbol
tables, in order. -/
def Module.setProblems (m : Module d) : List Problem := m.tables.flatMap SymbolTable.setProblems

/-- The check of a symbol table's dialect set decides
`SymbolTable.InDialectSet`. -/
theorem SymbolTable.setProblems_eq_nil_iff (t : SymbolTable d) :
    t.setProblems = [] ↔ t.InDialectSet := by
  simp only [SymbolTable.setProblems, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
    ite_none_eq_none, List.flatMap_eq_nil_iff, Func.setProblems]
  constructor
  · rintro ⟨hk, hw⟩
    refine ⟨hk, fun f hf x hx => ?_⟩
    have h := hw f hf
    split at h
    · cases h
    · rename_i hn
      simpa using List.find?_eq_none.mp hn x hx
  · rintro ⟨hk, hw⟩
    refine ⟨hk, fun f hf => ?_⟩
    split
    · rename_i x hx
      have := List.find?_some hx
      simp only [decide_eq_true_eq] at this
      exact absurd (hw f hf x (List.mem_of_find?_eq_some hx)) this
    · rfl

/-- The check of a module's dialect sets decides `Module.InDialectSet`. -/
theorem Module.setProblems_eq_nil_iff (m : Module d) : m.setProblems = [] ↔ m.InDialectSet := by
  simp only [Module.setProblems, List.flatMap_eq_nil_iff, SymbolTable.setProblems_eq_nil_iff,
    Module.InDialectSet]

instance (m : Module d) : Decidable m.InDialectSet :=
  decidable_of_iff _ m.setProblems_eq_nil_iff

variable [DialectSignature d] [DialectValidation d]

/-- A module passes validation with its dialect set when it is valid and
keeps to its set. -/
def Module.ValidInSet (m : Module d) : Prop := m.Valid ∧ m.InDialectSet

variable [DecidableEq d.Ty] [DecidableDialectValidation d]

/-- Every problem of a module: those of validity, then those of its dialect
set. -/
def Module.allProblems (m : Module d) : List Problem := m.problems ++ m.setProblems

/-- A module has no problem exactly when it passes validation with its
dialect set. -/
theorem Module.allProblems_eq_nil_iff (m : Module d) :
    m.allProblems = [] ↔ m.ValidInSet := by
  simp only [Module.allProblems, List.append_eq_nil_iff, m.problems_eq_nil_iff,
    m.setProblems_eq_nil_iff, Module.ValidInSet]

instance (m : Module d) : Decidable m.ValidInSet :=
  decidable_of_iff _ m.allProblems_eq_nil_iff

end Fir
