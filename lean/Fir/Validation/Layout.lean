import Fir.Validation.Scope

/-!
A module's data layout declares its memories (ADR-2026-11-12-1821). A valid
layout declares each memory once, and each entry gives a unit and a pointer
of at least one bit, an alignment that is a power of two, and numbers no
larger than `2^24 - 1`. Its byte order is `little`: M1 admits no other,
since no backend or harness yet uses a big-endian memory. A `big` entry is
read, and validation rejects it (the human's ruling of 2026-11-11 on #231).

A module has the memories that its layout declares, and memory 0 in any
case. Every pointer type that the module states names one of them: a
function's parameters, results, block arguments and op results, the types
that its ops carry in their attributes, and the parameters and results of
an item of a dialect's kind, at any depth. An op that writes values into the
units of a memory, such as the core's `memSet`, asks that the layout give
that memory units as wide as those values (`opUnits`). A
nested module has no layout of its own, so its types name the memories of
the module that holds it.

The layout of an aggregate describes a block of units of one memory
(ADR-2026-11-09-1550, ADR-2026-11-16-1546). It is valid when its numbers
are at most `2^64 - 1`, so that the text can write it, the module has its
memory, its alignment is valid as an entry's is, its types are valid and
name memories of the module, and its fields are placed: each field's type
may be a field, as the dialect of the type says (`fieldShape`), its offset
is a multiple of its type's alignment, that alignment is no larger than the
layout's, the field ends within the layout's size, and no two fields share
a unit. A repeated field takes its count times the units of one element
rounded up to the element's alignment (the human's ruling of 2026-11-16 on
#236), so a field of four `i24` in memory 0 takes 16 units, not 12. A field
that takes no units, such as a repeated field of no elements, which a C
flexible array member is, shares a unit with no field.

This section gives the rule of an alignment, which an `alloca` shares, of
an entry, of a layout, of the memories that a module's types name, and of
an aggregate's layout.
-/

namespace Fir

/-- A power of two: 1, 2, 4, and so on. A number other than 0 is one
exactly when it has no bit in common with the number below it. -/
def isPowerOfTwo (a : Nat) : Bool := a != 0 && a &&& (a - 1) == 0

example : [1, 2, 4, 1024].all isPowerOfTwo ∧ ![0, 3, 6, 12].any isPowerOfTwo := by decide

/-- An alignment that validation accepts, the one rule of an entry's
alignment and of an `alloca`'s: a power of two no larger than
`MemLayout.limit`. -/
abbrev MemLayout.ValidAlign (a : Nat) : Prop := isPowerOfTwo a ∧ a ≤ MemLayout.limit

/-- An entry of the data layout is valid: its memory is in range, its unit
and its pointers have at least one bit and are no wider than the limit, its
byte order is `little`, and the alignment it gives, if any, is a power of
two within the limit. -/
structure MemLayout.Valid (e : MemLayout) : Prop where
  mem : e.mem ≤ MemLayout.limit
  unit : 1 ≤ e.unit ∧ e.unit ≤ MemLayout.limit
  pointer : 1 ≤ e.pointer ∧ e.pointer ≤ MemLayout.limit
  little : e.order = .little
  align : ∀ a ∈ e.align, MemLayout.ValidAlign a

/-- A data layout is valid when each entry is, and it declares each memory
once. -/
structure DataLayout.Valid (l : DataLayout) : Prop where
  entries : ∀ e ∈ l, e.Valid
  unique : (l.map (·.mem)).Nodup

/-- Each memory of a valid layout has pointers of at least one bit, the
default memory included. -/
theorem DataLayout.pointer_pos {l : DataLayout} (hl : l.Valid) {n : Nat} {e : MemLayout}
    (h : l.memory? n = some e) : 0 < e.pointer := by
  unfold DataLayout.memory? at h
  split at h
  · rename_i he
    cases h
    exact (hl.entries _ (List.mem_of_find?_eq_some he)).pointer.1
  · split at h
    · cases h
      decide
    · cases h

variable {d : Dialect} [DialectValidation d]

/-- The layout has the memory that a type names, if it names one. -/
def DataLayout.HasMemoryOf (l : DataLayout) (t : d.Ty) : Prop := ∀ n ∈ tyMemory t, l.Declares n

instance DataLayout.decidableHasMemoryOf (l : DataLayout) (t : d.Ty) :
    Decidable (l.HasMemoryOf t) := by
  unfold DataLayout.HasMemoryOf
  cases tyMemory t <;> infer_instance

/-- The types that a function's ops carry in their attributes, op by op, at
any depth (`opTypes`). -/
def Func.attrTypes (f : Func d) : List d.Ty := f.allOps.flatMap fun o => opTypes o.op

/-- The memories whose units a function's ops write values of, each with
the width of those values, op by op, at any depth (`opUnits`). -/
def Func.unitWidths (f : Func d) : List (Nat × Nat) := f.allOps.flatMap fun o => opUnits o.op

/-- The layout gives the memory `q.1` units of `q.2` bits. -/
def DataLayout.HasUnits (l : DataLayout) (q : Nat × Nat) : Prop := (l.entry q.1).unit = q.2

instance DataLayout.decidableHasUnits (l : DataLayout) (q : Nat × Nat) :
    Decidable (l.HasUnits q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The memories that the types of a symbol table name are in the layout:
each type that each of its functions states, each that each of its items
of a dialect's kind states, and each that an op of each of its functions
carries in its attributes. And the layout gives each memory whose units an
op of its functions writes values of units as wide as those values. -/
structure SymbolTable.MemoriesIn (l : DataLayout) (t : SymbolTable d) : Prop where
  funcs : ∀ f ∈ t.funcs, ∀ ty ∈ f.types, l.HasMemoryOf ty
  dialectItems : ∀ i ∈ t.dialectItems, ∀ ty ∈ i.types, l.HasMemoryOf ty
  attrs : ∀ f ∈ t.funcs, ∀ ty ∈ f.attrTypes, l.HasMemoryOf ty
  units : ∀ f ∈ t.funcs, ∀ q ∈ f.unitWidths, l.HasUnits q

/-- The layout has each memory that the types of a module name, in each of
its symbol tables: its own and that of each nested module. -/
def Module.MemoriesDeclared (m : Module d) : Prop := ∀ t ∈ m.tables, t.MemoriesIn m.layout

/-- `u` rounded up to a multiple of `a`: the units that one element of a
repeated field takes, where one value of its type takes `u` units and its
alignment is `a`. -/
def roundUp (u a : Nat) : Nat := (u + a - 1) / a * a

example : roundUp 3 4 = 4 ∧ roundUp 8 8 = 8 ∧ roundUp 10 16 = 16 := by decide

/-- The units that a field takes, where one value of its type takes `u`
units aligned to `a`: `u` for one value, and for a repeated field its count
times `u` rounded up to `a`. -/
def Field.extent (f : Field d) (u a : Nat) : Nat :=
  match f.count with
  | none => u
  | some c => c * roundUp u a

/-- The units and the alignment of one value of a field's type in the memory
`n` of a module whose data layout is `l`, if the type may be a field. -/
def Field.shape (l : DataLayout) (n : Nat) (f : Field d) : Option (Nat × Nat) :=
  fieldShape l.entry n f.ty

/-- The units that a field takes in the memory `n` of a module whose data
layout is `l`: none when its type may not be a field. -/
def Field.units (l : DataLayout) (n : Nat) (f : Field d) : Nat :=
  match f.shape l n with
  | some (u, a) => f.extent u a
  | none => 0

/-- A field is placed in a layout of the memory `n` with the size `size` and
the alignment `align`: its type may be a field, its offset is a multiple of
its type's alignment, that alignment is no larger than `align`, and the
field ends within `size`. -/
def Field.Placed (l : DataLayout) (n size align : Nat) (f : Field d) : Prop :=
  match f.shape l n with
  | some (u, a) => a ∣ f.offset ∧ a ≤ align ∧ f.offset + f.extent u a ≤ size
  | none => False

instance Field.decidablePlaced (l : DataLayout) (n size align : Nat) (f : Field d) :
    Decidable (f.Placed l n size align) := by
  unfold Field.Placed
  split <;> infer_instance

/-- Two fields of a layout of the memory `n` share no unit: one ends before
the other starts, or one takes no units. -/
def Field.Apart (l : DataLayout) (n : Nat) (f g : Field d) : Prop :=
  f.offset + f.units l n ≤ g.offset ∨ g.offset + g.units l n ≤ f.offset ∨
    f.units l n = 0 ∨ g.units l n = 0

instance Field.decidableApart (l : DataLayout) (n : Nat) (f g : Field d) :
    Decidable (f.Apart l n g) := by
  unfold Field.Apart
  infer_instance

/-- An aggregate's layout is valid in a module whose data layout is `l`:
its numbers are within the limit, the module has its memory, its alignment is valid, each type it states is
valid and names a memory of the module, each field is placed, and no two
fields share a unit. -/
structure Aggregate.Valid (l : DataLayout) (a : Aggregate d) : Prop where
  limits : a.InLimits
  memory : l.Declares a.mem
  align : MemLayout.ValidAlign a.align
  types : ∀ t ∈ a.types, validTy t
  memories : ∀ t ∈ a.types, l.HasMemoryOf t
  fields : ∀ f ∈ a.fields, f.Placed l a.mem a.size a.align
  apart : a.fields.Pairwise (Field.Apart l a.mem)

/-- Each aggregate's layout of each symbol table of a module is valid in the
module's data layout. -/
def Module.AggregatesValid (m : Module d) : Prop :=
  ∀ t ∈ m.tables, ∀ a ∈ t.aggregates, a.Valid m.layout

end Fir
