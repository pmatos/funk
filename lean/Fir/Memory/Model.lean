/-!
Memory is made of _logical blocks_ (ADR-2026-11-09-1542). Each allocation is
a block of its own: an array of abstract units, with no address. A pointer
names the allocation it may access, its _provenance_, and an offset into it.
Two allocations never overlap, so a pass may assume that pointers into
different allocations do not alias.

This section gives one memory of that model. A module may have several
memories: the core's default memory and others, such as a GPU's shared
memory that a dialect adds (ADR-2026-10-29-2016). Each memory is a model of
its own, with its own allocations, and its unit of addressing has the width
that the module's data layout gives it, 8-bit bytes unless it says otherwise.
So the model is written once, for a unit of any width `u`. Sizes and offsets
count units, not bits.

A unit holds one of three things:

* concrete bits, `u` of them;
* poison: fresh memory holds poison, and so does memory that a poison value
  was stored to;
* a fragment of a pointer. A pointer stored to memory takes several units,
  and each holds its piece of the pointer and the number of the memory the
  pointer belongs to, so that a pointer copied unit by unit keeps its
  provenance, and is never read back as a pointer of another memory.

The model gives four primitive operations: allocating a block of a given
size, kind and alignment, freeing a block, and loading and storing a run of
units. Loads and stores are the accesses. An access is immediate UB, a
_fault_ below, when its pointer has no provenance for an allocation of the
memory, when its allocation is freed, or when the units it touches are not
all inside the allocation (ADR-2026-11-09-1542). Allocating and freeing
never fault: the run frees a call's stack allocations when the call returns
(ADR-2026-11-09-1548), and a heap allocation is freed by an external call,
which the world answers. A block records the alignment it was allocated
with, in units, so that the ops that access memory can check an access
against it; the accesses of this model do not. How a value of a type
becomes units, and how an op reaches these operations, are left to the ops
that use them.

A pointer of this model belongs to one memory, and its allocation id names an
allocation of that memory alone. Which memory a pointer belongs to is its
type's business, `ptr<N>`, not the pointer's: only a fragment of a pointer
stored to memory records it, since a unit has no type.

Provenance comes only from an allocation: a pointer has provenance for an
allocation because the allocation gave it, or because it was computed from
one that did. The model's laws hold of every pointer, but they speak of
aliasing only for pointers made so. A pointer that names an id the memory
has not yet allocated has no provenance for an allocation of the memory, so
every access through it faults.

The section after this one proves the laws that ops and passes rely on.
-/

namespace Fir.Memory

/-- An allocation's id: its place in the order of the memory's allocations.
An id is never reused, so a pointer into a freed allocation can never reach
a later one. -/
abbrev AllocId := Nat

/-- A pointer: the allocation it has provenance for, if any, and an offset
into that allocation, in units. The offset may be negative or past the end:
only an access through the pointer must be in bounds. A pointer without
provenance can access no allocation. -/
structure Pointer where
  prov : Option AllocId
  offset : Int
  deriving Repr, DecidableEq

/-- A unit of memory whose units are `u` bits wide: concrete bits, poison,
or the fragment `i` of the pointer `p` of the memory `m`. -/
inductive MemUnit (u : Nat) where
  | bits (b : BitVec u)
  | poison
  | frag (m : Nat) (p : Pointer) (i : Nat)
  deriving Repr, DecidableEq

/-- The kind of an allocation (ADR-2026-11-09-1542): a stack allocation
lives until the call that made it returns (ADR-2026-11-09-1548), a global
for the whole run (ADR-2026-11-09-1546), and a heap allocation comes from
an external call, such as one to `malloc`. Managed memory can be added as
another kind. -/
inductive AllocKind where
  | stack
  | global
  | heap
  deriving Repr, DecidableEq

/-- An allocation: its kind, its alignment, its units, and whether it is
still live. The alignment counts units: a block has no address, and the
alignment is what every address it is given is a multiple of, so that an
access can be checked against it (#231). A freed block keeps its units, but
no access may reach them. -/
structure Block (u : Nat) where
  kind : AllocKind
  align : Nat
  units : List (MemUnit u)
  live : Bool
  deriving Repr, DecidableEq

/-- A memory whose units are `u` bits wide: its allocations, in the order
they were made, so that the block with id `a` is `blocks[a]`. -/
structure Memory (u : Nat) where
  blocks : List (Block u)
  deriving Repr, DecidableEq

/-- Why an access is immediate UB (ADR-2026-11-09-1542). -/
inductive Fault where
  /-- The pointer has no provenance for an allocation of the memory. -/
  | noProvenance
  /-- The pointer's allocation is freed. -/
  | freed
  /-- The access touches a unit outside its allocation. -/
  | outOfBounds
  deriving Repr, DecidableEq

/-- The reason that a run which faults gives for its UB. -/
def Fault.reason : Fault → String
  | .noProvenance => "an access through a pointer without provenance"
  | .freed => "an access to a freed allocation"
  | .outOfBounds => "an access out of bounds"

variable {u : Nat}

/-- The `n` units of a block from offset `o` on. -/
def Block.read (b : Block u) (o n : Nat) : List (MemUnit u) :=
  (b.units.drop o).take n

/-- The block with its units from offset `o` on replaced by `us`. Its kind,
alignment and liveness stay as they were, and so does its size when the units fit in
it, from `o` to `o + |us|`. A store writes only units that fit, as its
access checks. -/
def Block.write (b : Block u) (o : Nat) (us : List (MemUnit u)) : Block u :=
  { b with units := b.units.take o ++ us ++ b.units.drop (o + us.length) }

/-- The block, freed: no longer live, with its kind, alignment and units. -/
def Block.kill (b : Block u) : Block u := { b with live := false }

namespace Memory

/-- The memory before anything is allocated. -/
def empty : Memory u := ⟨[]⟩

/-- Allocates a block of `n` units of kind `k`, aligned to `al` units. Its
units are poison, its id is one that no allocation had before, and it gives
the pointer to its first unit. -/
def alloc (M : Memory u) (k : AllocKind) (n al : Nat) : Pointer × Memory u :=
  (⟨some M.blocks.length, 0⟩, ⟨M.blocks ++ [⟨k, al, List.replicate n .poison, true⟩]⟩)

/-- Frees the allocation `a`: it stays in the memory, and no access may
reach it again. Freeing changes nothing else. It never faults: freeing an
allocation that is already freed, or that the memory does not have, changes
nothing. -/
def free (M : Memory u) (a : AllocId) : Memory u :=
  ⟨M.blocks.modify a Block.kill⟩

/-- Where an access of `n` units through `p` lands: the allocation, its
block, and the offset of the first unit, or the fault that makes the access
UB. -/
def locate (M : Memory u) (p : Pointer) (n : Nat) : Except Fault (AllocId × Block u × Nat) :=
  match p.prov with
  | none => .error .noProvenance
  | some a =>
    match M.blocks[a]? with
    | none => .error .noProvenance
    | some b =>
      if !b.live then .error .freed
      else if 0 ≤ p.offset ∧ p.offset + n ≤ b.units.length then .ok (a, b, p.offset.toNat)
      else .error .outOfBounds

/-- Loads `n` units through `p`: the units of its allocation from its
offset on, or the fault that makes the load UB. -/
def load (M : Memory u) (p : Pointer) (n : Nat) : Except Fault (List (MemUnit u)) := do
  let (_, b, o) ← M.locate p n
  pure (b.read o n)

/-- Stores the units `us` through `p`, in place of the units of its
allocation from its offset on, or gives the fault that makes the store UB.
No other unit, and no other allocation, changes. -/
def store (M : Memory u) (p : Pointer) (us : List (MemUnit u)) : Except Fault (Memory u) := do
  let (a, b, o) ← M.locate p us.length
  pure ⟨M.blocks.set a (b.write o us)⟩

end Memory

end Fir.Memory
