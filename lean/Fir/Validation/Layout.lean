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
function's parameters, results, block arguments and op results, and the
parameters and results of an item of a dialect's kind, at any depth. A
nested module has no layout of its own, so its types name the memories of
the module that holds it.

This section gives the rule of an entry, of a layout, and of the memories
that a module's types name.
-/

namespace Fir

/-- A power of two: 1, 2, 4, and so on. A number other than 0 is one
exactly when it has no bit in common with the number below it. -/
def isPowerOfTwo (a : Nat) : Bool := a != 0 && a &&& (a - 1) == 0

example : [1, 2, 4, 1024].all isPowerOfTwo ∧ ![0, 3, 6, 12].any isPowerOfTwo := by decide

/-- An entry of the data layout is valid: its memory is in range, its unit
and its pointers have at least one bit and are no wider than the limit, its
byte order is `little`, and the alignment it gives, if any, is a power of
two within the limit. -/
structure MemLayout.Valid (e : MemLayout) : Prop where
  mem : e.mem ≤ MemLayout.limit
  unit : 1 ≤ e.unit ∧ e.unit ≤ MemLayout.limit
  pointer : 1 ≤ e.pointer ∧ e.pointer ≤ MemLayout.limit
  little : e.order = .little
  align : ∀ a ∈ e.align, isPowerOfTwo a ∧ a ≤ MemLayout.limit

/-- A data layout is valid when each entry is, and it declares each memory
once. -/
structure DataLayout.Valid (l : DataLayout) : Prop where
  entries : ∀ e ∈ l, e.Valid
  unique : (l.map (·.mem)).Nodup

variable {d : Dialect} [DialectValidation d]

/-- The layout has the memory that a type names, if it names one. -/
def DataLayout.HasMemoryOf (l : DataLayout) (t : d.Ty) : Prop := ∀ n ∈ tyMemory t, l.Declares n

instance DataLayout.decidableHasMemoryOf (l : DataLayout) (t : d.Ty) :
    Decidable (l.HasMemoryOf t) := by
  unfold DataLayout.HasMemoryOf
  cases tyMemory t <;> infer_instance

/-- The memories that the types of a symbol table name are in the layout:
each type that each of its functions states, and each that each of its
items of a dialect's kind states. -/
structure SymbolTable.MemoriesIn (l : DataLayout) (t : SymbolTable d) : Prop where
  funcs : ∀ f ∈ t.funcs, ∀ ty ∈ f.types, l.HasMemoryOf ty
  dialectItems : ∀ i ∈ t.dialectItems, ∀ ty ∈ i.types, l.HasMemoryOf ty

/-- The layout has each memory that the types of a module name, in each of
its symbol tables: its own and that of each nested module. -/
def Module.MemoriesDeclared (m : Module d) : Prop := ∀ t ∈ m.tables, t.MemoriesIn m.layout

end Fir
