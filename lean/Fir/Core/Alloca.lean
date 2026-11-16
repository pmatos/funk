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

M1's validation accepts an integer type and a pointer type. A pointer type
`ptr<M>` takes the units of the width of memory `M`'s pointers in memory
`N`, the units its encoding takes. Its natural alignment in memory `N` is
the least power of two that is at least those units, but in memory `M`
itself it is the alignment that `M`'s layout entry gives its pointers,
which is that power of two unless the entry writes `align(A)`. A float
type has no encoding and takes no units; validation rejects it.

A field of an integer or a pointer type in an aggregate's layout of memory
`N` takes the units and the alignment of one value that `alloca` makes
there with no alignment of its own (`Ty.fieldShape_eq_allocaShape`,
ADR-2026-11-16-1546).
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

/-- The alignment of a value of the type `t` in the memory `ρ n` of a run
whose memories have the entries `lay`, when an op gives none: its natural
alignment there, but for a pointer of the memory `n` itself the alignment
that its entry gives its pointers (`MemLayout.alignment`), the natural one
unless the entry writes `align(A)`. -/
def Ty.defaultAlign (lay : N → MemLayout) (ρ : Mem → N) (n : Nat) (t : Ty) : Nat :=
  if t = .ptr n then (lay (ρ n)).alignment
  else t.naturalAlign (lay (ρ n)) fun j => (lay (ρ j)).pointer

/-- The units and the alignment of an allocation of `c` values of the type
`t` in the memory `ρ n` of a run whose memories have the entries `lay`,
with the alignment `a`, or the type's default alignment when `a` is
`none`. -/
def allocaShape (lay : N → MemLayout) (ρ : Mem → N) (t : Ty) (c : Nat) (a : Option Nat)
    (n : Nat) : Nat × Nat :=
  (c * t.units (lay (ρ n)) (fun j => (lay (ρ j)).pointer), a.getD (t.defaultAlign lay ρ n))

/-- A field of an aggregate's layout takes the units of one value that
`alloca` allocates, aligned as `alloca` aligns it when the op gives no
alignment (ADR-2026-11-16-1546): a layout of the memory `n` and an
allocation in it count the same units. -/
theorem Ty.fieldShape_eq_allocaShape (lay : Nat → MemLayout) (n : Nat) {t : Ty} (h : t.IsElem) :
    t.fieldShape lay n = some (allocaShape lay id t 1 none n) := by
  cases t with
  | int w => simp [Ty.fieldShape, allocaShape, Ty.units, Ty.defaultAlign, Ty.naturalAlign,
      pow2AtLeast_eq]
  | ptr m =>
    by_cases hm : m = n
    · subst hm
      simp [Ty.fieldShape, allocaShape, Ty.units, Ty.defaultAlign, MemLayout.alignment,
        MemLayout.naturalAlign, MemLayout.pointerUnits_eq, pow2AtLeast_eq]
    · simp [Ty.fieldShape, allocaShape, Ty.units, Ty.defaultAlign, Ty.naturalAlign, hm,
        pow2AtLeast_eq]
  | float => exact absurd h id

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

/-- Two pointers of memory 0 take 16 units of memory 0, aligned to 8; in a
memory 1 whose entry writes `align(4)` for its 32-bit pointers in 16-bit
units, a pointer of memory 1 takes 2 units aligned to 4, and one of memory
0 takes 4 units aligned to 4, its natural alignment there. -/
example : allocaShape (fun _ : Unit => MemLayout.default) (fun _ => ()) (.ptr 0) 2 none 0 =
    (16, 8) ∧
    let lay := fun n : Nat => if n = 1 then
      { mem := 1, unit := 16, pointer := 32, order := .little, align := some 4 } else
      MemLayout.default
    allocaShape lay id (.ptr 1) 1 none 1 = (2, 4) ∧ allocaShape lay id (.ptr 0) 1 none 1 = (4, 4) := by
  decide +kernel

end Fir.Core
