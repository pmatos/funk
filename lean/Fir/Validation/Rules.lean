import Fir.Validation.Dominance

/-!
The general rules of validation, for every dialect. A module is valid when
its symbols are unique, its location table is well formed, and each of its
functions is valid. A function is valid when its blocks, its ops and its
successors obey the rules below, and each op obeys its dialect's rule.

# Ops

An op in block `b` at index `i` of function `f` is valid when:

* it owns no region. Region rules come with the first dialect whose ops have
  regions (H6); no core op has one;
* each operand is a value the function defines, and the operand types are
  the op instance's operand types;
* the result types are the op instance's result types;
* it is a terminator exactly when it is the last op of its block, and it has
  as many successors as its op instance says;
* each value it uses is in scope: defined in the function and dominating the
  use;
* each symbol it refers to names a function of the module;
* its dialect's own rule holds;
* its location reference is a key of the module's location table (H8).
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
  (∀ s ∈ o.succs, f.SuccValid s) ∧
  (∀ x ∈ o.uses, f.InScope x b.label i) ∧
  (∀ g ∈ symbolRefs o.op, (ctx.symbols g).isSome) ∧
  validOp ⟨ctx.symbols, f.results⟩ o.op ∧
  o.loc ∈ ctx.locKeys

/-!
# Functions

A function is valid when:

* its body has an entry block, and the entry block declares no arguments of
  its own: its arguments are the function's parameters;
* the labels of its blocks are unique;
* the names of its values are unique: each value has one definition, as SSA
  requires;
* every type it states is valid for its dialect;
* every block holds at least one op, and every op is valid.
-/

/-- A function is valid in the context of its module. -/
structure Func.Valid (ctx : ModuleContext d) (f : Func d) : Prop where
  entry : ∃ e, f.blocks.head? = some e ∧ e.params = []
  labelsUnique : (f.blocks.map (·.label)).Nodup
  namesUnique : (f.defs.map (·.1)).Nodup
  types : ∀ t ∈ f.types, validTy t
  blocksNonEmpty : ∀ b ∈ f.blocks, b.body ≠ []
  ops : ∀ b ∈ f.blocks, ∀ (i : Nat) (o : Operation d),
    b.body[i]? = some o → f.OpValid ctx b i o

/-!
# The location table

Each entry of the table has a distinct reference, and the entries are in
increasing order of reference, so one table has one spelling. A location
that is built from others refers only to entries before it, so no location
refers to itself, directly or not. A fused location fuses at least two. A
source range starts at line 1 and column 1 or later, and does not end before
it starts.
-/

/-- A location is well formed. -/
def Location.WellFormed : Location → Prop
  | .range _ l₁ c₁ l₂ c₂ => 1 ≤ l₁ ∧ 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ (l₁ < l₂ ∨ (l₁ = l₂ ∧ c₁ ≤ c₂))
  | .fused locs => 2 ≤ locs.length
  | _ => True

/-- The location table is well formed. -/
def LocTable.Valid (t : LocTable) : Prop :=
  (t.map (·.1)).Pairwise (· < ·) ∧
  ∀ e ∈ t, e.2.WellFormed ∧ ∀ r ∈ e.2.refs, r < e.1 ∧ r ∈ t.map (·.1)

/-!
# Modules
-/

/-- The context in which a module's functions are checked. -/
def Module.context (m : Module d) : ModuleContext d :=
  ⟨m.symbols, m.locs.map (·.1)⟩

/--
A module is valid when each symbol names one function, its location table is
well formed, and each of its functions is valid.
-/
structure Module.Valid (m : Module d) : Prop where
  symbolsUnique : (m.funcs.map (·.name)).Nodup
  locs : LocTable.Valid m.locs
  funcs : ∀ f ∈ m.funcs, f.Valid m.context

end Fir
