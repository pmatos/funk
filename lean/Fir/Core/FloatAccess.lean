import Fir.Core.PtrAccess

/-!
# Float load and store rules

This section gives `loadFloat` and `storeFloat` their rules (#264). They
load and store a value of `float<e,m>` through a pointer of `ptr<N>`, in
the memory `N`, as `load` and `store` do for the integer of its
`1 + e + m` bits, since a float is its IEEE bit pattern
(ADR-2026-11-09-1549):

* a poison pointer is immediate UB, for the reason of `load` or `store`;
* otherwise each is the aligned access of the units that `1 + e + m` bits
  take in memory `N`, aligned to the op's alignment, or, when the op gives
  none, to the natural alignment of the float's size in memory `N`: the
  least power of two that is at least its units, as for the integer of its
  width (the human's ruling of 2026-11-15 on #397). An access that faults
  is immediate UB, for the reason of its fault;
* a store writes the encoding of the float's bits in the byte order of
  memory `N`, with the bits past `1 + e + m` in the last unit zero, or as
  many poison units for poison (the section on values in units);
* a load decodes the units it reads as the integer of `1 + e + m` bits,
  and gives the float with those bits: units of bits give their number,
  and a poison unit or a pointer's fragment gives poison.

So a float stored and loaded back is the same float, a NaN's payload and
sign included, and a float stored and loaded as the integer of its width,
or an integer stored and loaded as a float of its width, gives the same
bits: the two accesses touch the same units and read them the same way.
Whether a store faults depends on the allocations, not on what their units
hold, so a store reads no memory. The ordering does not change either
rule: M1's validation accepts only `nonatomic`. Each rule needs the memory
effect and the layout entry of its memory, so neither op has a rule in the
set monad (the section on the core's rules with memory).
-/

namespace Fir.Core

open Memory

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The value that units of the memory whose entry is `e` decode to as a
value of `float<fe,fm>`, in that memory's byte order: the integer of its
`1 + fe + fm` bits, as a result vector. -/
abbrev loadFloatResult (e : MemLayout) (fe fm : Nat) (us : List (MemUnit e.unit)) :
    HVector toType [Ty.float fe fm] :=
  .cons (decodeInt e.unit (floatWidth fe fm) e.order us : PoisonOr (BitVec (floatWidth fe fm))) .nil

/-- The rule of `loadFloat o fe fm a n`, in a monad with UB and the memory
effect on the memories of a run whose layout entries are `lay`, where the
run names the core's memory `x` as `ρ x`: UB on a poison pointer, and
otherwise the aligned load of the units of the integer of the float's
width from the memory `ρ n`, decoded. -/
def loadFloatRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (fe fm : Nat) (a : Option Nat) (n : Nat) :
    PoisonOr Pointer → m (HVector toType [Ty.float fe fm])
  | .poison => MonadUB.ub poisonPointer
  | .value p => loadFloatResult (lay (ρ n)) fe fm <$> MonadMemory.load (unit := unitsOf lay)
      (m := m) (ρ n) p (loadShape (lay (ρ n)) (floatWidth fe fm) a).1
      (loadShape (lay (ρ n)) (floatWidth fe fm) a).2

/-- The rule of `storeFloat o fe fm a n`, in a monad with UB and the memory
effect on the memories of a run whose layout entries are `lay`, where the
run names the core's memory `x` as `ρ x`: UB on a poison pointer, and
otherwise the aligned store of the encoding of the float's bits to the
memory `ρ n`, with no result. -/
def storeFloatRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (fe fm : Nat) (a : Option Nat) (n : Nat) :
    PoisonOr (BitVec (floatWidth fe fm)) → PoisonOr Pointer → m (HVector toType ([] : List Ty))
  | _, .poison => MonadUB.ub poisonStorePointer
  | v, .value p => (fun _ => .nil) <$> MonadMemory.store (unit := unitsOf lay) (m := m)
      (ρ n) p (storeUnits (lay (ρ n)) v) (storeAlign (lay (ρ n)) (floatWidth fe fm) a)

/-- A float store is the store of the integer of its width with the same
bits: the same units, at the same alignment. -/
theorem storeFloatRule_eq (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (fe fm : Nat) (a : Option Nat) (n : Nat) (v : PoisonOr (BitVec (floatWidth fe fm)))
    (p : PoisonOr Pointer) :
    storeFloatRule (m := m) lay ρ fe fm a n v p = storeRule lay ρ (floatWidth fe fm) a n v p := by
  cases p <;> rfl

/-- A float load decodes the units it reads to the bits that a load of the
integer of its width decodes them to: the float's result and the integer's
are the one decoding. -/
theorem loadFloatResult_bits (e : MemLayout) (fe fm : Nat) (us : List (MemUnit e.unit)) :
    loadFloatResult e fe fm us = .cons (decodeInt e.unit (floatWidth fe fm) e.order us) .nil ∧
      loadResult e (floatWidth fe fm) us =
        .cons (decodeInt e.unit (floatWidth fe fm) e.order us) .nil :=
  ⟨rfl, rfl⟩

/-- A float load reads the units that a load of the integer of its width
reads, at the same alignment. -/
theorem loadFloatRule_sameUnits (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (fe fm : Nat) (a : Option Nat) (n : Nat) (p : Pointer) :
    loadFloatRule (m := m) lay ρ fe fm a n (.value p) =
      loadFloatResult (lay (ρ n)) fe fm <$> MonadMemory.load (unit := unitsOf lay) (m := m)
        (ρ n) p (loadShape (lay (ρ n)) (floatWidth fe fm) a).1
        (loadShape (lay (ρ n)) (floatWidth fe fm) a).2 ∧
    loadRule (m := m) lay ρ (floatWidth fe fm) a n (.value p) =
      loadResult (lay (ρ n)) (floatWidth fe fm) <$> MonadMemory.load (unit := unitsOf lay)
        (m := m) (ρ n) p (loadShape (lay (ρ n)) (floatWidth fe fm) a).1
        (loadShape (lay (ρ n)) (floatWidth fe fm) a).2 :=
  ⟨rfl, rfl⟩

/-- In memory 0, an `f32` takes 4 units aligned to 4, an `f16` 2 aligned to
2, and a `float<2,1>` of 4 bits one unit aligned to 1. The `f32` whose bits
are `0x7fc00001`, a quiet NaN with a payload, is stored as its 4 bytes,
least significant first; a `float<2,1>` as one byte whose top 4 bits are
zero. -/
example : loadShape MemLayout.default (floatWidth 8 23) none = (4, 4) ∧
    loadShape MemLayout.default (floatWidth 5 10) none = (2, 2) ∧
    loadShape MemLayout.default (floatWidth 2 1) none = (1, 1) ∧
    storeUnits MemLayout.default (.value 0x7fc00001#(floatWidth 8 23)) =
      [.bits 0x01, .bits 0x00, .bits 0xc0, .bits 0x7f] ∧
    storeUnits MemLayout.default (.value 0xd#(floatWidth 2 1)) = [.bits 0x0d] := by
  decide +kernel

end Fir.Core
