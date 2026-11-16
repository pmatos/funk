import Fir.Memory.Model

/-!
# Addresses

A block has no address while the run only accesses it through pointers.
`ptr.expose` turns a pointer into an integer, and marks its allocation
_exposed_: from then on the allocation has an integer address, and an
integer may be turned back into a pointer to it (ADR-2026-11-09-1542). Only
exposed allocations have addresses. This section gives the memory model
what it needs for that: which addresses an allocation may be given, giving
it one, and the one canonical layout that `fir-ref` gives (#232). The ops
that expose a pointer and turn an integer back into one use them.

Each memory has its own addresses, from 0 up to `2 ^ P`, where `P` is the
width of the memory's pointers in its data layout. An allocation of `n`
units given the address `x` takes the addresses from `x` to `x + n`. The
address `x` _fits_ the allocation when:

* it is not 0, so that no allocation is at the address 0;
* it is a multiple of the allocation's alignment, which every address it
  may be given is (#231);
* the allocation ends below `2 ^ P`, so that the address one past its end
  is an address of the memory too, and is not 0;
* no other live allocation that has an address takes any address that this
  one would take.

The spec allows any address that fits. A freed allocation is not compared,
so its addresses may be given again: a later allocation may get exactly the
address of one that was freed, as native stack slots are reused. No law may
assume fresh addresses (the human's ruling of 2026-11-10 on #232). An
allocation keeps the address it was given for as long as the run lasts,
freed or not.

The _canonical layout_ is the assignment that `fir-ref` makes, one of those
the spec allows. It lays the allocations of a memory out in the order they
were made, from the address 1, each at the first multiple of its alignment
after the one before, with one unused address between them. So it is
deterministic: an allocation's canonical address depends only on the
allocations made before it, which never move. When the canonical address
does not fit, since the layout runs past `2 ^ P` or an allocation made
otherwise is in its way, the canonical layout gives the first address that
fits among those just after the allocations that have one. The section
after this one proves that it gives an address that fits whenever any
address fits.
-/

namespace Fir.Memory

variable {u : Nat}

/-- The least multiple of `al` that is at least `c`, when `al` is not 0. No
address is a multiple of 0 but 0 itself, and no allocation is at 0, so an
allocation aligned to 0 gets no address; `c` stands in for it. -/
def alignUp (c al : Nat) : Nat := if al = 0 then c else (c + al - 1) / al * al

#guard alignUp 1 4 == 4
#guard alignUp 4 4 == 4
#guard alignUp 5 4 == 8
#guard alignUp 7 1 == 7

/-- Whether the block `c` leaves room for `n` units from the address `x`: it
is freed, or has no address, or the addresses it takes and those from `x`
to `x + n` do not overlap. -/
def Block.leavesRoom (c : Block u) (x n : Nat) : Bool :=
  match c.addr with
  | none => true
  | some y => !c.live || decide (x + n ≤ y) || decide (y + c.units.length ≤ x)

/-- Whether every block of `bs` but the allocation `a` leaves room for `n`
units from the address `x`, where the first block of `bs` is the allocation
`i`. It walks the blocks in a loop. -/
def roomFrom (x n a : Nat) : Nat → List (Block u) → Bool
  | _, [] => true
  | i, c :: cs => (i == a || c.leavesRoom x n) && roomFrom x n a (i + 1) cs

/-- The block given the address `x`, unless it has one already: a block
keeps the first address it is given. Nothing else of it changes. -/
def Block.giveAddr (x : Nat) (b : Block u) : Block u :=
  if b.addr.isSome then b else { b with addr := some x }

namespace Memory

/-- The address of the allocation `a`, once it is exposed. -/
def addrOf (M : Memory u) (a : AllocId) : Option Nat := M.blocks[a]?.bind (·.addr)

/-- Whether the address `x` fits the allocation `a` of a memory whose
pointers are `P` bits wide: it is not 0, it is a multiple of the
allocation's alignment, the allocation ends below `2 ^ P`, and every other
allocation leaves room for it. No address fits an allocation the memory
does not have. -/
def fits (M : Memory u) (P a x : Nat) : Bool :=
  match M.blocks[a]? with
  | none => false
  | some b => decide (0 < x) && decide (b.align ∣ x) && decide (x + b.units.length < 2 ^ P) &&
      roomFrom x b.units.length a 0 M.blocks

/-- Gives the allocation `a` the address `x`, unless it has one already: an
allocation keeps the first address it is given. Nothing else changes. -/
def expose (M : Memory u) (a : AllocId) (x : Nat) : Memory u :=
  ⟨M.blocks.modify a (Block.giveAddr x)⟩

end Memory

/-- The canonical address of the allocation `a` of the blocks `bs`, when the
first of them is laid out from the address `c`: each at the first multiple
of its alignment from where the one before ends, plus one. It walks the
blocks in a loop. -/
def bumpFrom (c : Nat) : List (Block u) → AllocId → Nat
  | [], _ => c
  | b :: _, 0 => alignUp c b.align
  | b :: bs, a + 1 => bumpFrom (alignUp c b.align + b.units.length + 1) bs a

/-- The first address that fits the allocation `a`, of alignment `al`, just
after one of the blocks `cs`: the first multiple of `al` from where a live
block with an address ends. -/
def fitAfter (M : Memory u) (P a al : Nat) : List (Block u) → Option Nat
  | [] => none
  | c :: cs =>
    match c.addr with
    | some y =>
      if c.live && M.fits P a (alignUp (y + c.units.length) al) then
        some (alignUp (y + c.units.length) al)
      else fitAfter M P a al cs
    | none => fitAfter M P a al cs

namespace Memory

/-- The canonical address of the allocation `a`: where the allocations are
laid out in order from the address 1. -/
def bump (M : Memory u) (a : AllocId) : Nat := bumpFrom 1 M.blocks a

/-- The address that the canonical layout gives the allocation `a` of a
memory whose pointers are `P` bits wide: its canonical address when it
fits, or else the first address from 1 that fits, or the first that fits
just after an allocation with an address. None when none of them fits. -/
def canonical (M : Memory u) (P : Nat) (a : AllocId) : Option Nat :=
  if M.fits P a (M.bump a) then some (M.bump a)
  else
    match M.blocks[a]? with
    | none => none
    | some b =>
      if M.fits P a (alignUp 1 b.align) then some (alignUp 1 b.align)
      else fitAfter M P a b.align M.blocks

end Memory

-- Two allocations of 4 and 2 units, aligned to 4 and 8, are laid out at 4
-- and 16: the first takes 4 to 8, and 9 is the first address after the gap.
#guard ((Memory.empty.alloc .stack 4 4).2.alloc .stack 2 8 : Pointer × Memory 8).2.bump 1 == 16
#guard ((Memory.empty.alloc .stack 4 4).2 : Memory 8).canonical 64 0 == some 4
-- An allocation of 300 bytes does not fit a memory of 8-bit pointers.
#guard ((Memory.empty.alloc .stack 300 1).2 : Memory 8).canonical 8 0 == none

end Fir.Memory
