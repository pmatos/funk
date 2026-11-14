/-!
A module's data layout describes its memories (ADR-2026-11-09-1542). Each
memory has a number, `N` in the pointer type `ptr<N>`. For each memory it
declares, the layout gives:

* the width of its unit of addressing, in bits: sizes and offsets in the
  memory count its units;
* the width of its pointers, in bits;
* its byte order, the order of the units of a value that spans several,
  `little` or `big`;
* the alignment of its pointers, in units, when it is not their natural
  alignment;
* whether it is non-integral, as LLVM's `ni:` marks an address space: no
  pointer of a non-integral memory becomes an integer.

Memory 0, the default memory, is in every module. A layout that does not
declare it gives it the default: 8-bit units, 64-bit pointers, little
endian, natural alignment and integral. A module whose text has no layout
has the empty layout, so it has memory 0 alone, with the default
(ADR-2026-11-12-1821).

The text writes the layout on one line after the dialect set, and the
validation chapter says which layouts are valid. A run of a module gives
each of its memories its entry, and the semantics with memory gives each op
the entry of each memory it names, so an op that loads or stores reads the
unit, the byte order and the pointer width of the memory it accesses from
its entry, and an allocation reads the units and the natural alignment of
its type. This section gives the byte orders, a memory's entry, the
layout, and the widths and alignments that an entry gives.
-/

namespace Fir

/-- The order of the units of a value that spans several units of a
memory: `little` puts the least significant unit first, at the lowest
offset, and `big` the most significant. -/
inductive ByteOrder where
  | little
  | big
  deriving Repr, DecidableEq, Inhabited

/--
The entry of the data layout for one memory.

* `mem` is the memory's number.
* `unit` is the width of its unit of addressing, in bits.
* `pointer` is the width of its pointers, in bits.
* `order` is its byte order.
* `align` is the alignment of its pointers, in units, when the entry gives
  one; `none` is their natural alignment.
* `nonIntegral` marks a memory whose pointers never become integers, as
  LLVM's `ni:` does.
-/
structure MemLayout where
  mem : Nat
  unit : Nat
  pointer : Nat
  order : ByteOrder
  align : Option Nat := none
  nonIntegral : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- A data layout: an entry for each memory it declares, in the order the
text writes them. Nothing sorts or merges them. -/
abbrev DataLayout := List MemLayout

/-- The largest number that an entry of the layout gives: a memory, a
width or an alignment, `2^24 - 1`, the bound of an integer type's width
and of a pointer type's memory. -/
def MemLayout.limit : Nat := 2 ^ 24 - 1

/-- The default memory's entry when the layout does not declare it: 8-bit
units, 64-bit pointers, little endian, natural alignment, integral. -/
def MemLayout.default : MemLayout :=
  { mem := 0, unit := 8, pointer := 64, order := .little }

/-- The entry of memory `n`: the first that the layout declares for it, or
the default for memory 0. Another memory that the layout does not declare
has none: the module does not have it. -/
def DataLayout.memory? (l : DataLayout) (n : Nat) : Option MemLayout :=
  match l.find? (·.mem == n) with
  | some e => some e
  | none => if n = 0 then some MemLayout.default else none

/-- The module has memory `n`: it is the default memory, or the layout
declares it. -/
def DataLayout.Declares (l : DataLayout) (n : Nat) : Prop := (l.memory? n).isSome

instance DataLayout.decidableDeclares (l : DataLayout) (n : Nat) : Decidable (l.Declares n) :=
  inferInstanceAs (Decidable ((l.memory? n).isSome = true))

/-- Every module has the default memory. -/
theorem DataLayout.declares_zero (l : DataLayout) : l.Declares 0 := by
  unfold Declares memory?
  split <;> simp

/-- A memory that a layout lists is one that it declares. -/
theorem DataLayout.declares_of_mem {l : DataLayout} {e : MemLayout} (h : e ∈ l) :
    l.Declares e.mem := by
  unfold Declares memory?
  split
  · rfl
  · rename_i hn
    exact absurd (List.find?_eq_none.mp hn e h) (by simp)

/-- The empty layout, which a module without a layout line has, declares
the default memory alone. -/
theorem DataLayout.declares_nil {n : Nat} : DataLayout.Declares [] n ↔ n = 0 := by
  unfold Declares memory?
  by_cases h : n = 0 <;> simp [h]

/-- The entry that a run of a module with the layout `l` gives its memory
`n`: the one that `l` declares for it, or the default memory's when `l`
declares none. Memory 0 has an entry in every layout. Validation rejects
every type that names a memory that `l` does not declare, so a valid module
never reaches the default for any other memory; an invalid one may, since a
run does not validate what it runs. -/
def DataLayout.entry (l : DataLayout) (n : Nat) : MemLayout := (l.memory? n).getD .default

/-- The entry of a memory that the layout declares is its declared one. -/
theorem DataLayout.entry_of_memory {l : DataLayout} {n : Nat} {e : MemLayout}
    (h : l.memory? n = some e) : l.entry n = e := by
  simp [entry, h]

/-- How many units a pointer of the memory takes: its width over the unit's,
rounded up. -/
def MemLayout.pointerUnits (e : MemLayout) : Nat := (e.pointer + e.unit - 1) / e.unit

/-- The natural alignment of the memory's pointers, in units: the least
power of two that is at least the units a pointer takes. -/
def MemLayout.naturalAlign (e : MemLayout) : Nat := e.pointerUnits.nextPowerOfTwo

/-- The alignment of the memory's pointers, in units: the entry's own, or
the natural one. -/
def MemLayout.alignment (e : MemLayout) : Nat := e.align.getD e.naturalAlign

/-- How many units a value of `w` bits takes in the memory: `w` over the
unit's width, rounded up. An integer of `iN` takes `N` bits, so it takes
`e.bitsUnits N` units, as many as its encoding writes. -/
def MemLayout.bitsUnits (e : MemLayout) (w : Nat) : Nat := (w + e.unit - 1) / e.unit

/-- The natural alignment of the integer type `iN`, `N = w`, in the memory,
in units: the least power of two that is at least the units it takes, as
for pointers. In memory 0, `i8` has 1, `i24` 4, `i32` 4, `i64` 8 and
`i128` 16 (the human's ruling of 2026-11-14 on #378). -/
def MemLayout.intAlign (e : MemLayout) (w : Nat) : Nat := (e.bitsUnits w).nextPowerOfTwo

/-- A pointer takes the units of its width. -/
theorem MemLayout.pointerUnits_eq (e : MemLayout) : e.pointerUnits = e.bitsUnits e.pointer := rfl

/-- The natural alignments of integers in the default memory, from the
ruling. -/
example : [1, 8, 24, 32, 64, 128].map MemLayout.default.intAlign = [1, 1, 4, 4, 8, 16] := by
  decide +kernel

/-- The default memory's pointers take 8 units, aligned to 8. -/
example : MemLayout.default.pointerUnits = 8 ∧ MemLayout.default.alignment = 8 := by decide +kernel

end Fir
