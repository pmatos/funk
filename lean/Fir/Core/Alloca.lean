import Fir.Core.Encode
import Fir.Core.OpEffects
import Fir.Execution.MemoryObligations
import Fir.Syntax.Layout

/-!
# Stack allocation rules

This section gives `alloca` its rule (#231; the human's ruling of
2026-11-14 on #378). `alloca` allocates room for a number of values of a
type in the memory of its result, `ptr<N>`, and gives the pointer to the
first unit of the allocation:

* the allocation takes the count times the units of the type in memory
  `N`: an integer of `iW` takes `W` bits, rounded up to whole units, as
  many as its encoding writes;
* it is aligned to the op's alignment, or, when the op gives none, to the
  type's natural alignment in memory `N`, the least power of two that is at
  least its units. In memory 0, `i8` has 1, `i32` 4, `i64` 8 and `i128` 16;
* it has the op's kind. M1's validation accepts only `stack`, and a stack
  allocation lives until the call that made it returns: the frame of the
  call frees it (the section on the memories of a run).

Its units are poison until a store writes them, and the pointer has
provenance for it, at offset 0. Allocating never faults, so `alloca` is
never UB, and its result is never poison. The rule needs the memory effect
and the layout entry of the memory it allocates in, so `alloca` has no rule
in the set monad (the section on the core's rules with memory).

M1's validation accepts only an integer type. The rule counts a pointer
type `ptr<M>` by the width of the pointers of memory `M`, the units its
encoding takes, and gives a float type, which has no encoding, no units;
no valid module reaches either yet.
-/

namespace Fir.Core

open Memory

/-- The units that a value of the type `t` takes in a memory whose entry is
`e`, where the pointers of memory `M` are `ptrBits M` bits wide: its bits,
rounded up to whole units, the units its encoding takes. A float type has
no encoding, and takes none. -/
def Ty.units (e : MemLayout) (ptrBits : Nat → Nat) : Ty → Nat
  | .int w => e.bitsUnits w
  | .ptr m => e.bitsUnits (ptrBits m)
  | .float _ _ => 0

/-- An integer type takes the units of its encoding (`Ty.units?`). -/
theorem Ty.units?_int (l : DataLayout) (e : MemLayout) (ptrBits : Nat → Nat) (w : Nat) :
    (Ty.int w).units? l e.unit = some ((Ty.int w).units e ptrBits) := rfl

/-- The natural alignment of the type `t` in a memory whose entry is `e`, in
units: the least power of two that is at least the units it takes. -/
def Ty.naturalAlign (e : MemLayout) (ptrBits : Nat → Nat) (t : Ty) : Nat :=
  (t.units e ptrBits).nextPowerOfTwo

/-- The natural alignment of `iN` is the one that the layout gives it. -/
theorem Ty.naturalAlign_int (e : MemLayout) (ptrBits : Nat → Nat) (w : Nat) :
    (Ty.int w).naturalAlign e ptrBits = e.intAlign w := rfl

variable {N : Type} {m : Type → Type} [Monad m]

/-- The units and the alignment of an allocation of `c` values of the type
`t` in the memory `ρ n` of a run whose memories have the entries `lay`,
with the alignment `a`, or the type's natural alignment when `a` is
`none`. -/
def allocaShape (lay : N → MemLayout) (ρ : Mem → N) (t : Ty) (c : Nat) (a : Option Nat)
    (n : Nat) : Nat × Nat :=
  let ptrBits := fun j => (lay (ρ j)).pointer
  (c * t.units (lay (ρ n)) ptrBits, a.getD (t.naturalAlign (lay (ρ n)) ptrBits))

/-- The rule of `alloca k t c a n`, in a monad with the memory effect on the
memories of a run whose layout entries are `lay`, where the run names the
core's memory `x` as `ρ x`: it allocates the units of `c` values of `t` in
the memory `ρ n`, of the kind `k`, with its alignment, and gives the
pointer to the allocation. -/
def allocaRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) (n : Nat) :
    m (HVector toType [Ty.ptr n]) :=
  (fun p => .cons (.value p) .nil) <$>
    MonadMemory.alloc (ρ n) k (allocaShape lay ρ t c a n).1 (allocaShape lay ρ t c a n).2

/-- Four `i32` take 16 units of memory 0, aligned to 4; twelve `i8` aligned
to 4 take 12. -/
example : allocaShape (fun _ : Unit => MemLayout.default) (fun _ => ()) (.int 32) 4 none 0 =
    (16, 4) ∧
    allocaShape (fun _ : Unit => MemLayout.default) (fun _ => ()) (.int 8) 12 (some 4) 0 =
      (12, 4) := by
  decide +kernel

end Fir.Core
