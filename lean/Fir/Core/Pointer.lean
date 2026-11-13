import Fir.Core.Values

/-!
# Pointer offset rules

This section gives `ptradd` its rule (#231). A pointer of the memory model
is the allocation it has provenance for, if any, and an offset into it, in
the units of its memory (ADR-2026-11-09-1542). `ptradd` moves a pointer of
`ptr<N>` by the integer that an `iW` holds, read as signed:

* the result has the same provenance, so it may access the same
  allocation, and no other;
* its offset is the pointer's offset plus the integer, in units of the
  memory `N`. So `ptradd` by `-1` of a pointer at offset 3 gives the
  pointer at offset 2, and by 4 the pointer at offset 7.

The offset is a mathematical integer: it does not wrap, at any width of
the integer, and it may leave the bounds of the allocation, or go below
its start. Only an access through the result must be in bounds, so
moving a pointer out of its allocation and back is not UB, and neither
is a pointer that is never used. The rule needs no data layout: it counts
units of the pointer's memory, whatever their width.

`ptradd` is never UB, and gives poison only for a poison operand: a
poison pointer, or a poison integer, gives a poison pointer
(ADR-2026-10-29-2006). A pointer without provenance stays without it:
moving it gives no allocation to access.
-/

namespace Fir.Core

open Memory

/-- A pointer moved by `k` units: its provenance, and its offset plus `k`. -/
def movePointer (p : Pointer) (k : Int) : Pointer := { p with offset := p.offset + k }

/-- The rule of `ptradd`: the pointer moved by the integer, read as signed,
and poison when either operand is poison. -/
def ptraddValue : PoisonOr Pointer → PoisonOr (BitVec w) → PoisonOr Pointer
  | .value p, .value k => .value (movePointer p k.toInt)
  | _, _ => .poison

-- `ptradd` by `-1` and by 4 of a pointer at offset 3 of the allocation 0.
#guard ptraddValue (.value ⟨some 0, 3⟩) (.value (-1 : BitVec 8)) == .value ⟨some 0, 2⟩
#guard ptraddValue (.value ⟨some 0, 3⟩) (.value (4 : BitVec 64)) == .value ⟨some 0, 7⟩
-- The offset does not wrap, and may leave the allocation in either direction.
#guard ptraddValue (.value ⟨some 1, 0⟩) (.value (-128 : BitVec 8)) == .value ⟨some 1, -128⟩
#guard ptraddValue (.value ⟨some 1, 2 ^ 64⟩) (.value (2 ^ 63 - 1 : BitVec 64)) ==
  .value ⟨some 1, 2 ^ 64 + 2 ^ 63 - 1⟩
-- An `i1` holds `0` or `-1`.
#guard ptraddValue (.value ⟨some 2, 5⟩) (.value (1 : BitVec 1)) == .value ⟨some 2, 4⟩
-- A pointer without provenance stays without it.
#guard ptraddValue (.value ⟨none, 0⟩) (.value (8 : BitVec 32)) == .value ⟨none, 8⟩
-- A poison operand gives poison.
#guard ptraddValue .poison (.value (1 : BitVec 32)) == .poison
#guard ptraddValue (.value ⟨some 0, 0⟩) (.poison : PoisonOr (BitVec 32)) == .poison

end Fir.Core
