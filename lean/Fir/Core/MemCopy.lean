import Fir.Core.Store
import Fir.Execution.MemoryCopyLaws

/-!
# Copy and move rules

This section gives `memCopy` its rule (#234; ADR-2026-11-09-1551). A copy,
written `memcpy`, and a move, written `memmove`, carry `len` units of the
memory `N` from the source pointer to the destination pointer, both of
`ptr<N>`, where `len` is the unsigned value of an `iW`. Each unit comes
across exactly, bits, poison and pointer fragments alike, so a copied
pointer keeps its provenance. The rule takes the length first:

* a length of 0 does nothing and gives no result, whatever the pointers
  are, poison, dangling or without provenance included (the human's
  ruling of 2026-11-18 on #234, Q1);
* otherwise a poison pointer is immediate UB: a pointer with no
  provenance in its place faults, so the UB is the op's own rule (the
  section on poison obligations with memory);
* otherwise a copy whose two ranges partly overlap is immediate UB: they
  lie in one allocation, at different offsets less than `len` apart. Two
  pointers with no provenance lie in no allocation, so their ranges never
  overlap, and the copy of units faults through them.
  Equal ranges are allowed, and so are disjoint ones (the human's ruling
  of 2026-11-18 on #234, Q2). A move allows any overlap;
* otherwise it is the copy of units of the section on copies of units in
  the state layer: a load of `len` units through the source, then a store
  of them through the destination, each an access aligned to one unit, so
  never misaligned. The load leaves the memories as they were, so a move
  whose ranges overlap writes what the source held before it began. An
  access that faults is immediate UB, for the reason of its fault.

A poison length runs as some length: the rule chooses `W` bits, as
`freeze` does, and runs with their unsigned value. So a poison length is
UB wherever some length is, as a poison operand is UB wherever some value
in its place is (ADR-2026-10-29-2006), and otherwise it carries the units
of some length. A choice keeps the memories and reads none.

Whether the overlap check fails depends only on the two pointers and the
length, not on the memories. The ordering does not change the rule: M1's
validation accepts only `nonatomic`. The rule needs the memory effect and
the layout entry of its memory, so `memCopy` has no rule in the set monad
(the section on the core's rules with memory).
-/

namespace Fir.Core

open Memory

/-- Whether the ranges of `len` units through `d` and `s` partly overlap:
the pointers have the provenance of one allocation, and different offsets
less than `len` apart. Equal ranges do not partly overlap, and neither do
ranges through pointers with no provenance. -/
def partlyOverlap (d s : Pointer) (len : Nat) : Bool :=
  d.prov.isSome && d.prov == s.prov && d.offset != s.offset &&
    decide ((d.offset - s.offset).natAbs < len)

/-- Why a copy or a move through a poison pointer is UB. -/
def poisonCopyPointer : String := "a copy or move through a poison pointer"

/-- Why a copy whose ranges partly overlap is UB. -/
def overlapCopy : String := "a memcpy whose ranges partly overlap"

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The rule of a copy or a move of the kind `k` of a defined length of
`len` units of the core's memory `n`, from `s` to `d`, in a monad with UB
and the memory effect on the memories of a run whose layout entries are
`lay`, where the run names the core's memory `x` as `ρ x`: nothing for a
length of 0, UB on a poison pointer, UB on a copy whose ranges partly
overlap, and otherwise the copy of units in the memory `ρ n`, aligned to
one unit, with no result. -/
def copyLenRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (k : CopyKind) (n len : Nat) (d s : PoisonOr Pointer) : m (HVector toType ([] : List Ty)) :=
  if len = 0 then pure .nil else
    match d, s with
    | .value d, .value s =>
      if k == .copy && partlyOverlap d s len then MonadUB.ub overlapCopy
      else (fun _ => .nil) <$> copyUnits (unit := unitsOf lay) (m := m) (ρ n) d s len 1 1
    | _, _ => MonadUB.ub poisonCopyPointer

/-- The rule of `memCopy k o w n` on the destination `d`, the source `s`
and the length `l`, an `iW` with `W = w`, in a monad with choice, UB and
the memory effect: the rule of the length's unsigned value, or, for a
poison length, of the unsigned value of `W` bits that it chooses. -/
def memCopyRule [MonadChoice m] (lay : N → MemLayout) (ρ : Mem → N)
    [MonadMemory N (unitsOf lay) m] (k : CopyKind) (w n : Nat) (d s : PoisonOr Pointer) :
    PoisonOr (BitVec w) → m (HVector toType ([] : List Ty))
  | .value l => copyLenRule lay ρ k n l.toNat d s
  | .poison => MonadChoice.choose w >>= fun l => copyLenRule lay ρ k n l.toNat d s

-- Ranges of 4 units 2 apart in one allocation partly overlap; equal ranges,
-- ranges 4 apart, ranges in two allocations, and ranges through pointers
-- with no provenance do not.
#guard partlyOverlap ⟨some 0, 2⟩ ⟨some 0, 0⟩ 4 && partlyOverlap ⟨some 0, 0⟩ ⟨some 0, 2⟩ 4
#guard !partlyOverlap ⟨some 0, 3⟩ ⟨some 0, 3⟩ 4 && !partlyOverlap ⟨some 0, 4⟩ ⟨some 0, 0⟩ 4 &&
  !partlyOverlap ⟨some 0, 2⟩ ⟨some 1, 0⟩ 4 && !partlyOverlap ⟨none, 2⟩ ⟨none, 0⟩ 4

end Fir.Core
