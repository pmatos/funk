import Fir.Validation.Dominance

/-!
The general rules of validation, for every dialect. A module is valid when
its location table is well formed and each of its symbol tables, its own
and that of each nested module, is valid: its symbols are unique, each of
its functions is valid, each of its items of a dialect's kind is valid, and
its dialect set names each dialect once, by a word. A function is valid
when its blocks, its ops and its successors obey the rules below, and each
op obeys its dialect's rule.

# Ops

An op is checked where it stands: at an index of a block of a function, in
the context of its module. The rules below give, in order:

* the context of a function: what the rules read of its module;
* a valid successor: a branch passes one value of the right type for each
  argument of its target, which is not the entry block;
* valid regions of an op: each has the kind that the op instance states, a
  kind that the dialect registers, and obeys the rule of its kind;
* a valid op: its regions; its types, its place in its block, its
  successors, the values it uses, the symbols it refers to, its dialect's
  own rule and its location;
* a valid op inside a region of an op: the rules of a valid op that do not
  depend on the kind of its region. Where it may stand, where its
  successors go and which values it may use are the rule of its region's
  kind.
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

/--
The regions of the op `o` of function `f` are valid: they have the kinds
that its op instance states, in order, and each is of a kind, named by a
word, that the dialect registers, and obeys the rule of that kind. A kind is a word of a
dialect, so a region of the core's kind is never valid inside an op.
-/
def Func.RegionsValid (ctx : ModuleContext d) (f : Func d) (o : Operation d) : Prop :=
  o.regions.map (·.kind) = (regionKinds o.op).map some ∧
  ∀ r ∈ o.regions, ∀ k, r.kind = some k → isWord k ∧
    k ∈ regionKindNames (d := d) ∧ validRegion (DialectView.id d) k ⟨ctx.symbols⟩ f r

/-- An op whose regions are valid owns no region of the core's kind. -/
theorem Func.RegionsValid.noCoreRegion {ctx : ModuleContext d} {f : Func d} {o : Operation d}
    (h : f.RegionsValid ctx o) : o.ownsCoreRegion = false := by
  unfold Operation.ownsCoreRegion
  rw [List.any_eq_false]
  intro r hr
  have hm : r.kind ∈ o.regions.map (·.kind) := List.mem_map_of_mem hr
  rw [h.1] at hm
  obtain ⟨k, _, hk⟩ := List.mem_map.mp hm
  simp [← hk]

/-- An op that owns no region, of an op instance that states none, has
valid regions. -/
theorem Func.regionsValid_of_nil {ctx : ModuleContext d} {f : Func d} {o : Operation d}
    (h : o.regions = []) (hk : regionKinds o.op = []) : f.RegionsValid ctx o :=
  ⟨by rw [h, hk]; rfl, fun r hr => absurd (h ▸ hr) List.not_mem_nil⟩

/-- The op `o` at index `i` of block `b` of function `f` is valid. -/
def Func.OpValid (ctx : ModuleContext d) (f : Func d) (b : Block d) (i : Nat)
    (o : Operation d) : Prop :=
  f.RegionsValid ctx o ∧
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

/--
The op `o`, in a region of an op of function `f`, is valid as far as the
general rules go: its regions, its types, its successors' count, each
successor's label is a name and each value it passes is one that `f`
defines, the symbols it refers to, its dialect's own rule and its location.
The rule of its region's kind says the rest: where the op may stand, where
its successors go and which values it may use.
-/
def Func.InnerOpValid (ctx : ModuleContext d) (f : Func d) (o : Operation d) : Prop :=
  f.RegionsValid ctx o ∧
  o.operands.map f.typeOf = (sig o.op).map some ∧
  o.results.map (·.2) = returnTypes o.op ∧
  o.succs.length = succCount o.op ∧
  (isTerminator o.op = false → o.succs = []) ∧
  (∀ s ∈ o.succs, isName s.label ∧ ∀ a ∈ s.args, (f.typeOf a).isSome) ∧
  (∀ g ∈ symbolRefs o.op, (ctx.symbols g).isSome) ∧
  validOp ⟨ctx.symbols, f.results⟩ o.op ∧
  o.loc ∈ ctx.locKeys

/-- The ops of the regions of the op `o`: those of each block of each of its
regions, not deeper. -/
def Operation.innerOps (o : Operation d) : List (Operation d) :=
  o.regions.flatMap fun r => r.blocks.flatMap (·.body)

/-- The block `b` is a block of a region of an op of a block of `all`. -/
def Block.InRegionOf (all : List (Block d)) (b : Block d) : Prop :=
  ∃ b₀ ∈ all, ∃ o ∈ b₀.body, ∃ r ∈ o.regions, b ∈ r.blocks

omit [DialectSignature d] [DialectValidation d] in
theorem Block.InRegionOf.mono {all all' : List (Block d)} {b : Block d}
    (h : ∀ x ∈ all, x ∈ all') : Block.InRegionOf all b → Block.InRegionOf all' b
  | ⟨b₀, hb₀, rest⟩ => ⟨b₀, h b₀ hb₀, rest⟩

section
omit [DialectSignature d] [DialectValidation d]

/-- Each block of a list is among its blocks at any depth. -/
theorem Block.mem_allBlocks {b : Block d} :
    ∀ {bs : List (Block d)}, b ∈ bs → b ∈ Block.allBlocks bs
  | ⟨_, _, _⟩ :: _, h => by
    rw [Block.allBlocks]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (Block.mem_allBlocks h))

mutual
/-- A block of these regions, at any depth, is a block of one of them, or of
a region of an op of one of their blocks. -/
theorem Region.mem_allBlocks_cases : ∀ {rs : List (Region d)} {b : Block d},
    b ∈ Region.allBlocks rs → (∃ r ∈ rs, b ∈ r.blocks) ∨ Block.InRegionOf (Region.allBlocks rs) b
  | [], _, h => by simp [Region.allBlocks] at h
  | ⟨k, bs⟩ :: rs, b, h => by
    have hsub₁ : ∀ x ∈ Block.allBlocks bs, x ∈ Region.allBlocks (⟨k, bs⟩ :: rs) := fun x hx => by
      rw [Region.allBlocks]; exact List.mem_append_left _ hx
    have hsub₂ : ∀ x ∈ Region.allBlocks rs, x ∈ Region.allBlocks (⟨k, bs⟩ :: rs) := fun x hx => by
      rw [Region.allBlocks]; exact List.mem_append_right _ hx
    rw [Region.allBlocks] at h
    rcases List.mem_append.1 h with h | h
    · rcases Block.mem_allBlocks_cases h with h | h
      · exact .inl ⟨_, List.mem_cons_self, h⟩
      · exact .inr (h.mono hsub₁)
    · rcases Region.mem_allBlocks_cases h with ⟨r, hr, hb⟩ | h
      · exact .inl ⟨r, List.mem_cons_of_mem _ hr, hb⟩
      · exact .inr (h.mono hsub₂)

/-- A block of these blocks at any depth is one of them, or a block of a
region of an op of one of them, at any depth. -/
theorem Block.mem_allBlocks_cases : ∀ {bs : List (Block d)} {b : Block d},
    b ∈ Block.allBlocks bs → b ∈ bs ∨ Block.InRegionOf (Block.allBlocks bs) b
  | [], _, h => by simp [Block.allBlocks] at h
  | ⟨l, ps, body⟩ :: bs, b, h => by
    have hsub₁ : ∀ x ∈ Operation.regionBlocks body,
        x ∈ Block.allBlocks (⟨l, ps, body⟩ :: bs) := fun x hx => by
      rw [Block.allBlocks]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
    have hsub₂ : ∀ x ∈ Block.allBlocks bs, x ∈ Block.allBlocks (⟨l, ps, body⟩ :: bs) :=
      fun x hx => by
        rw [Block.allBlocks]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)
    have hself : ⟨l, ps, body⟩ ∈ Block.allBlocks (⟨l, ps, body⟩ :: bs) := by
      rw [Block.allBlocks]; exact List.mem_cons_self
    rw [Block.allBlocks] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl List.mem_cons_self
    rcases List.mem_append.1 h with h | h
    · rcases Operation.mem_regionBlocks_cases h with ⟨o, ho, r, hr, hb⟩ | h
      · exact .inr ⟨_, hself, o, ho, r, hr, hb⟩
      · exact .inr (h.mono hsub₁)
    · rcases Block.mem_allBlocks_cases h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (h.mono hsub₂)

/-- A block of the regions of these ops, at any depth, is a block of a
region of one of them, or of a region of an op of a block below them. -/
theorem Operation.mem_regionBlocks_cases : ∀ {os : List (Operation d)} {b : Block d},
    b ∈ Operation.regionBlocks os → (∃ o ∈ os, ∃ r ∈ o.regions, b ∈ r.blocks) ∨
      Block.InRegionOf (Operation.regionBlocks os) b
  | [], _, h => by simp [Operation.regionBlocks] at h
  | ⟨rs', op, xs, ss, regions, loc⟩ :: os, b, h => by
    have hsub₁ : ∀ x ∈ Region.allBlocks regions,
        x ∈ Operation.regionBlocks (⟨rs', op, xs, ss, regions, loc⟩ :: os) := fun x hx => by
      rw [Operation.regionBlocks]; exact List.mem_append_left _ hx
    have hsub₂ : ∀ x ∈ Operation.regionBlocks os,
        x ∈ Operation.regionBlocks (⟨rs', op, xs, ss, regions, loc⟩ :: os) := fun x hx => by
      rw [Operation.regionBlocks]; exact List.mem_append_right _ hx
    rw [Operation.regionBlocks] at h
    rcases List.mem_append.1 h with h | h
    · rcases Region.mem_allBlocks_cases h with ⟨r, hr, hb⟩ | h
      · exact .inl ⟨_, List.mem_cons_self, r, hr, hb⟩
      · exact .inr (h.mono hsub₁)
    · rcases Operation.mem_regionBlocks_cases h with ⟨o, ho, r, hr, hb⟩ | h
      · exact .inl ⟨o, List.mem_cons_of_mem _ ho, r, hr, hb⟩
      · exact .inr (h.mono hsub₂)
end

end

omit [DialectSignature d] [DialectValidation d] in
/-- A block of a function at any depth is a block of its body, or a block of
a region of an op of one of its blocks at any depth. -/
theorem Func.mem_allBlocks_cases {f : Func d} {b : Block d} (h : b ∈ f.allBlocks) :
    b ∈ f.blocks ∨ Block.InRegionOf f.allBlocks b :=
  Block.mem_allBlocks_cases h

/-- A function whose ops own no region, at any depth, has no op inside a
region. -/
theorem Func.inner_of_noRegions {ctx : ModuleContext d} {f : Func d}
    (h : ∀ b ∈ f.allBlocks, ∀ o ∈ b.body, o.regions.isEmpty = true) :
    ∀ b ∈ f.allBlocks, ∀ o ∈ b.body, ∀ o' ∈ o.innerOps, f.InnerOpValid ctx o' := by
  intro b hb o ho o' ho'
  simp [Operation.innerOps, List.isEmpty_iff.1 (h b hb o ho)] at ho'

/-!
# Functions

A function is valid when its body is a region of the core's kind, a
control-flow graph (ADR-2026-10-29-2005), its entry block declares no
arguments, every block is reachable from the entry, its labels and value
names are unique and can be written in the text, every type it states is
valid, every block holds at least one op, each of them valid, every op
inside a region of an op obeys the general rules, and the function obeys
its dialect's own rule over a whole function.
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
  inner : ∀ b ∈ f.allBlocks, ∀ o ∈ b.body, ∀ o' ∈ o.innerOps, f.InnerOpValid ctx o'
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
An item of a dialect's kind is valid, in the context of its table's
symbols, when its kind is a word of a dialect that the dialect registers,
its parameters have distinct names, its types are valid, its attributes can
be written, and it obeys the dialect's rule for items (ADR-2026-11-10-2224).
-/
structure DialectItem.Valid (ctx : FuncContext d) (i : DialectItem d) : Prop where
  kind : isDialectWord i.kind
  registered : i.kind ∈ itemKindNames (d := d)
  names : ∀ x ∈ i.params, isName x.1
  namesUnique : (i.params.map (·.1)).Nodup
  types : ∀ t ∈ i.types, validTy t
  attrs : Attr.AllWritable i.attrs
  dialect : validItem (DialectView.id d) ctx i

/--
A symbol table is valid, in a module whose location table has the
references `keys`, when each symbol names one item, each of its functions is
valid in the table's context, each of its items of a dialect's kind is valid
with the table's symbols, and its dialect set names each dialect once, by a
word. Which dialects the set may
name, and that the table's words name only those, is the rule of a
module's dialect set, in the chapter on sums of dialects: it reads the
words of the module, which the dialect's text gives.
-/
structure SymbolTable.Valid (keys : List LocRef) (t : SymbolTable d) : Prop where
  symbolsUnique : (t.items.map Item.name).Nodup
  funcs : ∀ f ∈ t.funcs, f.Valid (t.context keys)
  dialectItems : ∀ i ∈ t.dialectItems, i.Valid ⟨t.symbols⟩
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
  refine ⟨symbolsUnique, funcs, fun i hi => ?_, dialectNames, dialectsUnique⟩
  obtain ⟨j, hj, he⟩ := List.mem_filterMap.mp hi
  have := flat j hj
  cases j <;> simp_all [Item.func?, Item.dialect?]

/-!
# Valid op instances

An op instance's types are its operand types and its result types. They
are _valid_ when validation accepts each of them, as it accepts the types
of every value that a valid function defines. For the core dialect that is
`iN` with 1 ≤ N ≤ 16,777,215, a valid float format, and `ptr`, the
pointer of the default memory. Every op of a valid function
has an op instance with valid types, as the section on what the lawful
class gives proves, and the poison obligations speak only of such op
instances (ADR-2026-11-02-1515).
-/

/-- Validation accepts the types of the op instance `op`: each of its
operand types and each of its result types is valid for its dialect. -/
def TypesValid (op : d.Op) : Prop :=
  (∀ t ∈ sig op, validTy t) ∧ ∀ t ∈ returnTypes op, validTy t

end Fir
