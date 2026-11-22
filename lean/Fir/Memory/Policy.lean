import Fir.Memory.Address
import Fir.Memory.Frames

/-!
# Address policies

The spec allows an exposed allocation any address that it may be given,
below, and a run gives one of them each time it exposes an allocation that
has none. Which one is the run's _address policy_: for a memory, it
sees each allocation's shape and address, and proposes an address for the
allocation being exposed, or none. It sees nothing that refinement may
change, such as the units an allocation holds, so memories that refine each
other get the same proposal.

An allocation may be given an address that fits it. A freed allocation
may also be given any address in range that is a multiple of its
alignment, the address of a live allocation included: no access reaches
it, and a native stack slot that it held may hold a live allocation by
the time a dangling pointer to it is exposed. The memory model takes the
proposal when it may be given, and the canonical address otherwise. So the
address given may always be given, whatever the policy proposes, and the
canonical layout is the policy that proposes nothing. No address is given
exactly when none may be: the memory has run out of addresses. The spec has
no outcome for that, as allocating has none, so it is UB (the human's
ruling of 2026-11-18 on #232, Q5).

Each memory's addresses run from `1` to `2 ^ P - 1`, where `P` is the width
of its pointers in the data layout (the human's ruling of 2026-11-18 on
#232, Q4). No allocation is at the address 0, and the address one past the
end of every allocation is an address of the memory, not 0.

Exposing a pointer gives its allocation's address plus the pointer's offset,
wrapped at the pointer width: the integer that `ptr_expose` returns. A
pointer with no provenance gives its offset, wrapped, and so does one whose
provenance names no allocation of the memory, which no run makes. An allocation keeps
the first address it is given, so exposing it again gives the same address
and changes nothing.
-/

namespace Fir.Memory

variable {u : Nat}

/-- What an address policy sees of a block: its shape, which is its kind,
alignment, size, liveness and constness, and its address. -/
abbrev Place := (AllocKind × Nat × Nat × Bool × Bool) × Option Nat

/-- What an address policy sees of a memory: each block's shape and
address, in the order the allocations were made. -/
def Memory.places (M : Memory u) : List Place := M.blocks.map fun b => (b.shape, b.addr)

/-- An address policy for one memory: from the places of its blocks, the
address it proposes for the allocation `a`, or none. -/
abbrev Policy := List Place → AllocId → Option Nat

/-- The address policy of the canonical layout: it proposes no address, so
each allocation exposed gets its canonical one. -/
def Policy.canonical : Policy := fun _ _ => none

namespace Memory

/-- Whether the address `x` may be given to the allocation `a`, in the
range of addresses from `lo` to `hi`: it fits, or `a` is freed and `x` is
in the range and a multiple of its alignment. No access reaches a freed
allocation, and a live one may take its addresses, so a freed one takes
room from none: it may be given the address of a live allocation, as a
native stack slot is reused. -/
def admits (M : Memory u) (lo hi a x : Nat) : Bool :=
  M.fits lo hi a x || match M.blocks[a]? with
    | some b => !b.live && decide (lo ≤ x) && decide (b.align ∣ x) &&
        decide (x + b.units.length ≤ hi)
    | none => false

/-- The address given to the allocation `a` when the policy proposes none
that may be given: its canonical address, or else, for a freed allocation,
the first multiple of its alignment from `lo`, when it may be given. -/
def fallback (M : Memory u) (lo hi a : Nat) : Option Nat :=
  match M.canonical lo hi a with
  | some z => some z
  | none => match M.blocks[a]? with
    | some b => if M.admits lo hi a (alignUp lo b.align) then some (alignUp lo b.align) else none
    | none => none

/-- The address given to the allocation `a`, in the range of addresses
from `lo` to `hi`, when the policy proposes `y?`: the proposal when it may
be given, and else the fallback. None when no address may be given. -/
def choose (M : Memory u) (lo hi a : Nat) : Option Nat → Option Nat
  | some y => if M.admits lo hi a y then some y else M.fallback lo hi a
  | none => M.fallback lo hi a

end Memory

/-- The bound of the addresses of a memory whose pointers are `P` bits
wide: an allocation ends at it at the latest, so the address one past its
end is below `2 ^ P`. The lowest address is 1. -/
def addrHi (P : Nat) : Nat := 2 ^ P - 1

/-- The reason that a run gives for its UB when it exposes an allocation
that no address may be given. -/
def noAddressReason : String := "an exposure that no address fits"

namespace Memories

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Exposes the pointer `p` of the memory `x`, whose pointers are `P` bits
wide, under the address policy `g`: its allocation's address plus its
offset, wrapped at `P` bits, with the memories after, where the allocation
has that address. An allocation that has no address is given one, by
`choose`. A pointer with no provenance, or whose allocation `x` does not
have, gives its offset. None when no address may be given. -/
def expose (S : Memories Mem unit) (x : Mem) (g : Policy) (P : Nat) (p : Pointer) :
    Option (BitVec P × Memories Mem unit) :=
  match p.prov with
  | none => some (BitVec.ofInt P p.offset, S)
  | some a =>
    match (S.mem x).blocks[a]? with
    | none => some (BitVec.ofInt P p.offset, S)
    | some b =>
      match b.addr with
      | some y => some (BitVec.ofInt P (y + p.offset), S)
      | none => ((S.mem x).choose 1 (addrHi P) a (g (S.mem x).places a)).map fun (y : Nat) =>
          (BitVec.ofInt P (y + p.offset), S.set x ((S.mem x).expose a y))

end Memories

end Fir.Memory
