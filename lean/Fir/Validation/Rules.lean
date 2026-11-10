import Fir.Validation.Dominance

/-!
The general rules of validation, for every dialect. A module is valid when
its location table is well formed and each of its symbol tables, its own
and that of each nested module, is valid: its symbols are unique, each of
its functions is valid, and its dialect set names each dialect once, by a
word. A function is valid when its blocks, its ops
and its successors obey the rules below, and each op obeys its dialect's
rule.

# Ops

An op is checked where it stands: at an index of a block of a function, in
the context of its module. The rules below give, in order:

* the context of a function: what the rules read of its module;
* a valid successor: a branch passes one value of the right type for each
  argument of its target, which is not the entry block;
* a valid op: it owns no region; its types, its place in its block, its
  successors, the values it uses, the symbols it refers to, its dialect's
  own rule and its location.
-/

namespace Fir

variable {d : Dialect} [DialectSignature d] [DialectValidation d]

/--
The context in which a module's functions are checked: its symbol table and
the keys of its location table.
-/
structure ModuleContext (d : Dialect) where
  symbols : Name → Option (FuncType d)
  locKeys : List LocRef

/--
A successor is valid when it names a block of the function other than the
entry, and passes one value of the right type for each of that block's
arguments (H1). The entry block has no predecessors.
-/
def Func.SuccValid (f : Func d) (s : Succ) : Prop :=
  f.entryLabel? ≠ some s.label ∧
  ∃ tgt, f.block? s.label = some tgt ∧
    s.args.map f.typeOf = tgt.params.map (some ·.2)

/-- The op `o` at index `i` of block `b` of function `f` is valid. -/
def Func.OpValid (ctx : ModuleContext d) (f : Func d) (b : Block d) (i : Nat)
    (o : Operation d) : Prop :=
  o.regions = [] ∧
  o.operands.map f.typeOf = (sig o.op).map some ∧
  o.results.map (·.2) = returnTypes o.op ∧
  (isTerminator o.op = true ↔ i + 1 = b.body.length) ∧
  o.succs.length = succCount o.op ∧
  (isTerminator o.op = false → o.succs = []) ∧
  (∀ s ∈ o.succs, f.SuccValid s) ∧
  (∀ x ∈ o.uses, f.InScope x b.label i) ∧
  (∀ g ∈ symbolRefs o.op, (ctx.symbols g).isSome) ∧
  validOp ⟨ctx.symbols, f.results⟩ o.op ∧
  o.loc ∈ ctx.locKeys

/-!
# Functions

A function is valid when its body is a region of the core's kind, a
control-flow graph (ADR-2026-10-29-2005), its entry block declares no
arguments, every block is reachable from the entry, its labels and value
names are unique and can be written in the text, every type it states is
valid, every block holds at least one op, each of them valid, and the
function obeys its dialect's own rule over a whole function.
-/

/-- A function is valid in the context of its module. -/
structure Func.Valid (ctx : ModuleContext d) (f : Func d) : Prop where
  bodyKind : f.body.kind = none
  entry : ∃ e, f.blocks.head? = some e ∧ e.params = []
  reachable : ∀ b ∈ f.blocks, f.Reachable b.label
  labelsUnique : (f.blocks.map (·.label)).Nodup
  namesUnique : (f.defs.map (·.1)).Nodup
  names : ∀ x ∈ f.defs, isName x.1
  labels : ∀ b ∈ f.allBlocks, isName b.label
  types : ∀ t ∈ f.types, validTy t
  blocksNonEmpty : ∀ b ∈ f.blocks, b.body ≠ []
  ops : ∀ b ∈ f.blocks, ∀ (i : Nat) (o : Operation d),
    b.body[i]? = some o → f.OpValid ctx b i o
  dialect : validFunc (DialectView.id d) ⟨ctx.symbols⟩ f

/-!
# The location table

Each entry of the table has a distinct reference, and the entries are in
increasing order of reference, so one table has one spelling. A location
that is built from others refers only to entries before it, so no location
refers to itself, directly or not. A fused location fuses at least two.
Every reference, line and column is below 2³².

A source range starts at line 1 or later, and does not end before it starts.
When both of its columns are known (not 0) and it starts and ends on one
line, its end column is at least its start column. An end equal to the
start is an empty range.
-/

/-- A location is well formed. -/
def Location.WellFormed : Location → Prop
  | .range _ l₁ c₁ l₂ c₂ => 1 ≤ l₁ ∧ (l₁ < l₂ ∨ (l₁ = l₂ ∧ (c₁ = 0 ∨ c₂ = 0 ∨ c₁ ≤ c₂)))
  | .fused locs => 2 ≤ locs.length
  | _ => True

/-- The location table is well formed. -/
def LocTable.Valid (t : LocTable) : Prop :=
  (t.map (·.1)).Pairwise (· < ·) ∧ t.InLimits ∧
  ∀ e ∈ t, e.2.WellFormed ∧ ∀ r ∈ e.2.refs, r < e.1 ∧ r ∈ t.map (·.1)

/-!
# Modules
-/

/-- The context in which a module's functions are checked. -/
def Module.context (m : Module d) : ModuleContext d :=
  ⟨m.symbols, m.locs.map (·.1)⟩

/-- The context in which the functions of a symbol table are checked, in a
module whose location table has the references `keys`: the table's own
symbols, and the module's one location table. -/
def SymbolTable.context (keys : List LocRef) (t : SymbolTable d) : ModuleContext d :=
  ⟨t.symbols, keys⟩

/--
A symbol table is valid, in a module whose location table has the
references `keys`, when each symbol names one item, function or nested
module, each of its functions is valid in the table's context, and its
dialect set names each dialect once, by a word. Which dialects the set may
name, and that the table's words name only those, is the rule of a
module's dialect set, in the chapter on sums of dialects: it reads the
words of the module, which the dialect's text gives.
-/
structure SymbolTable.Valid (keys : List LocRef) (t : SymbolTable d) : Prop where
  symbolsUnique : (t.items.map Item.name).Nodup
  funcs : ∀ f ∈ t.funcs, f.Valid (t.context keys)
  dialectNames : ∀ x ∈ t.dialects, isWord x
  dialectsUnique : t.dialects.Nodup

/--
A module is valid when its location table is well formed and each of its
symbol tables is valid: its own, and that of each module nested in it, at
any depth (ADR-2026-11-10-1510). One location table serves them all.
-/
structure Module.Valid (m : Module d) : Prop where
  locs : LocTable.Valid m.locs
  tables : ∀ t ∈ m.tables, t.Valid (m.locs.map (·.1))

/-- A valid module's own table is valid. -/
theorem Module.Valid.table {m : Module d} (h : m.Valid) : m.table.Valid (m.locs.map (·.1)) :=
  h.tables _ (List.mem_cons_self ..)

/-- Each function of a valid module is valid in the module's context. -/
theorem Module.Valid.funcs {m : Module d} (h : m.Valid) : ∀ f ∈ m.funcs, f.Valid m.context :=
  h.table.funcs

/-- Each function of a valid module has a symbol of its own. -/
theorem Module.Valid.symbolsUnique {m : Module d} (h : m.Valid) : (m.funcs.map (·.name)).Nodup :=
  (funcNames_sublist m.items).nodup h.table.symbolsUnique

/-- A valid module's dialect set names each dialect by a word. -/
theorem Module.Valid.dialectNames {m : Module d} (h : m.Valid) : ∀ x ∈ m.dialects, isWord x :=
  h.table.dialectNames

/-- A valid module's dialect set names each dialect once. -/
theorem Module.Valid.dialectsUnique {m : Module d} (h : m.Valid) : m.dialects.Nodup :=
  h.table.dialectsUnique

/-- A module with no nested module is valid when its location table and its
own table are. -/
theorem Module.valid_of_flat {m : Module d} (flat : ∀ i ∈ m.items, i.func?.isSome)
    (symbolsUnique : (m.items.map Item.name).Nodup) (locs : LocTable.Valid m.locs)
    (funcs : ∀ f ∈ m.funcs, f.Valid m.context) (dialectNames : ∀ x ∈ m.dialects, isWord x)
    (dialectsUnique : m.dialects.Nodup) : m.Valid := by
  refine ⟨locs, fun t ht => ?_⟩
  simp only [Module.tables, Item.tablesIn_eq_nil flat, List.mem_singleton] at ht
  subst ht
  exact ⟨symbolsUnique, funcs, dialectNames, dialectsUnique⟩

/-!
# Valid op instances

An op instance's types are its operand types and its result types. They
are _valid_ when validation accepts each of them, as it accepts the types
of every value that a valid function defines. For the core dialect that is
`iN` with 1 ≤ N ≤ 16,777,215, never `ptr`. Every op of a valid function
has an op instance with valid types, as the section on what the lawful
class gives proves, and the poison obligations speak only of such op
instances (ADR-2026-11-02-1515).
-/

/-- Validation accepts the types of the op instance `op`: each of its
operand types and each of its result types is valid for its dialect. -/
def TypesValid (op : d.Op) : Prop :=
  (∀ t ∈ sig op, validTy t) ∧ ∀ t ∈ returnTypes op, validTy t

end Fir
