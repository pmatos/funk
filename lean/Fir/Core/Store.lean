import Fir.Core.Load

/-!
# Store rules

This section gives `store` its rule (#231). `store` stores a value of `iW`
through a pointer of `ptr<N>`, into the memory `N`, and gives no result:

* a poison pointer is immediate UB, as for `load`: some defined pointer in
  its place faults, as one with no provenance does, so a poison operand is
  UB by the op's own rules (the section on poison obligations with memory);
* otherwise it is the aligned store of the encoding of the value in the
  units that `iW` takes in memory `N`, in that memory's byte order (the
  section on values in units), aligned as a load of `iW` is: to the op's
  alignment, or, when the op gives none, to the natural alignment of `iW`
  in memory `N`. The encoding of a value of `W` bits takes them rounded up
  to whole units, and sets the bits past `W` in the last unit to zero (the
  human's ruling of 2026-11-11 on #231). The encoding of poison is as many
  poison units, so a store of poison is not UB: it makes those units
  poison, and a load of them gives poison again;
* an access that faults is immediate UB, for the reason of its fault: out
  of bounds, to a freed allocation, through a pointer without provenance,
  or misaligned (the section on aligned access laws). Whether it faults
  depends on the allocations, not on what their units hold, so a store
  reads no memory.

The ordering does not change the rule: M1's validation accepts only
`nonatomic`. The rule needs the memory effect and the layout entry of the
memory it writes, so `store` has no rule in the set monad (the section on
the core's rules with memory).
-/

namespace Fir.Core

open Memory

/-- The alignment of a store of `iW`, `W = w`, to a memory whose entry is
`e`: the alignment `a`, or the natural alignment of `iW` in that memory when
`a` is `none`, as for a load. -/
def storeAlign (e : MemLayout) (w : Nat) (a : Option Nat) : Nat :=
  a.getD (e.intAlign w)

/-- A store is aligned as a load of the same type is. -/
theorem storeAlign_eq (e : MemLayout) (w : Nat) (a : Option Nat) :
    storeAlign e w a = (loadShape e w a).2 := rfl

/-- The units that a value of `iW`, `W = w`, takes in a memory whose entry
is `e`: its encoding in that memory's unit and byte order. -/
abbrev storeUnits (e : MemLayout) {w : Nat} (v : PoisonOr (BitVec w)) : List (MemUnit e.unit) :=
  encodeInt e.unit e.order v

/-- Why a store through a poison pointer is UB. -/
def poisonStorePointer : String := "a store through a poison pointer"

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The rule of `store o w a n`, in a monad with UB and the memory effect on
the memories of a run whose layout entries are `lay`, where the run names
the core's memory `x` as `ρ x`: UB on a poison pointer, and otherwise the
aligned store of the value's encoding to the memory `ρ n`, with no
result. -/
def storeRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m] (w : Nat)
    (a : Option Nat) (n : Nat) :
    PoisonOr (BitVec w) → PoisonOr Pointer → m (HVector toType ([] : List Ty))
  | _, .poison => MonadUB.ub poisonStorePointer
  | v, .value p => (fun _ => .nil) <$> MonadMemory.store (unit := unitsOf lay) (m := m)
      (ρ n) p (storeUnits (lay (ρ n)) v) (storeAlign (lay (ρ n)) w a)

/-- An `i32` stored to memory 0 is 4 bytes, least significant first,
aligned to 4; an `i1` is one byte, its bits past the first zero; poison is
poison units. -/
example : storeAlign MemLayout.default 32 none = 4 ∧
    storeUnits MemLayout.default (.value 0x04030201#32) = [.bits 1, .bits 2, .bits 3, .bits 4] ∧
    storeUnits MemLayout.default (.value 1#1) = [.bits 1] ∧
    storeUnits MemLayout.default (.poison : PoisonOr (BitVec 16)) = [.poison, .poison] := by
  decide +kernel

end Fir.Core
