import Fir.Core.Alloca

/-!
# Load rules

This section gives `load` its rule (#231). `load` loads a value of `iW`
through a pointer of `ptr<N>`, from the memory `N`:

* a poison pointer is immediate UB. Some defined pointer in its place
  faults, as one with no provenance does, so a poison operand is UB by the
  op's own rules (the section on poison obligations with memory);
* otherwise it is the aligned load of the units that `iW` takes in memory
  `N`, its `W` bits rounded up to whole units, aligned to the op's
  alignment, or, when the op gives none, to the natural alignment of `iW`
  in memory `N`: the least power of two that is at least its units. An
  access that faults is immediate UB, for the reason of its fault: out of
  bounds, to a freed allocation, through a pointer without provenance, or
  misaligned (the section on aligned access laws);
* the units it loads are decoded as a value of `iW`, in the byte order of
  memory `N` (the section on values in units): units of bits give their
  number, cut to `W` bits, so the bits past `W` in the last unit are
  ignored, and any poison unit or pointer fragment among them gives poison.
  So a load from fresh memory gives poison, and so does a punned load of a
  pointer's units (the human's rulings of 2026-11-11 on #231).

The ordering does not change the rule: M1's validation accepts only
`nonatomic`. The rule needs the memory effect and the layout entry of the
memory it reads, so `load` has no rule in the set monad (the section on
the core's rules with memory).
-/

namespace Fir.Core

open Memory

/-- The units and the alignment of a load of `iW`, `W = w`, from a memory
whose entry is `e`: the units that `W` bits take, and the alignment `a`, or
the natural alignment of `iW` in that memory when `a` is `none`. -/
def loadShape (e : MemLayout) (w : Nat) (a : Option Nat) : Nat × Nat :=
  (e.bitsUnits w, a.getD (e.intAlign w))

/-- Why a load through a poison pointer is UB. -/
def poisonPointer : String := "a load through a poison pointer"

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The value that units of the memory whose entry is `e` decode to as a
value of `iW`, `W = w`, in that memory's byte order, as a result vector. -/
abbrev loadResult (e : MemLayout) (w : Nat) (us : List (MemUnit e.unit)) :
    HVector toType [Ty.int w] :=
  .cons (decodeInt e.unit w e.order us : PoisonOr (BitVec w)) .nil

/-- The rule of `load o w a n`, in a monad with UB and the memory effect on
the memories of a run whose layout entries are `lay`, where the run names
the core's memory `x` as `ρ x`: UB on a poison pointer, and otherwise the
aligned load of the units of `iW` from the memory `ρ n`, decoded. -/
def loadRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m] (w : Nat)
    (a : Option Nat) (n : Nat) : PoisonOr Pointer → m (HVector toType [Ty.int w])
  | .poison => MonadUB.ub poisonPointer
  | .value p => loadResult (lay (ρ n)) w <$> MonadMemory.load (unit := unitsOf lay) (m := m)
      (ρ n) p (loadShape (lay (ρ n)) w a).1 (loadShape (lay (ρ n)) w a).2

/-- An `i32` takes 4 units of memory 0, aligned to 4; an `i1` takes 1,
aligned to 1, or to 4 when the op says so. -/
example : loadShape MemLayout.default 32 none = (4, 4) ∧
    loadShape MemLayout.default 1 none = (1, 1) ∧
    loadShape MemLayout.default 1 (some 4) = (1, 4) := by
  decide +kernel

end Fir.Core
