import Fir.Core.Store

/-!
# Pointer load and store rules

This section gives `loadPtr` and `storePtr` their rules (#231; the human's
ruling of 2026-11-14 on #382). They load and store a value of `ptr<M>`
through a pointer of `ptr<N>`, in the memory `N`, as `load` and `store` do
for an integer:

* a poison pointer is immediate UB, for the reason of `load` or `store`;
* otherwise each is the aligned access of the units that a pointer of
  memory `M` takes in memory `N`: the width of `M`'s pointers, rounded up to
  whole units of `N`. It is aligned to the op's alignment, or, when the op
  gives none, to the default alignment of `ptr<M>` in memory `N`, as an
  `alloca` of `ptr<M>` is (the section on stack allocation rules). An access
  that faults is immediate UB, for the reason of its fault;
* a store writes the pointer's encoding, its fragments with the memory `M`
  in the byte order of memory `N`, or as many poison units for poison
  (the section on values in units). A pointer copied unit by unit keeps its
  provenance;
* a load decodes the units it reads as a pointer of memory `M`: only the
  fragments of one pointer of `M`, in order, give that pointer, and any
  other units give poison. So a load from fresh memory, from units of bits,
  from a pointer of another memory or from a pointer partly overwritten
  gives poison (the human's rulings of 2026-11-11 on #231, Q3).

Whether a store faults depends on the allocations, not on what their
units hold, so a store reads no memory. The ordering does not change either
rule: M1's validation accepts only `nonatomic`. Each rule needs the memory
effect and the layout entries of the memories, so neither op has a rule in
the set monad (the section on the core's rules with memory).
-/

namespace Fir.Core

open Memory

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The units and the alignment of an access of a value of `ptr<M>`,
`M = mp`, in the memory `ρ n` of a run whose memories have the entries `lay`:
the units of `ptr<M>` there, and the alignment `a`, or the default
alignment of `ptr<M>` there when `a` is `none`, as for an `alloca` of one
`ptr<M>`. -/
def ptrShape (lay : N → MemLayout) (ρ : Mem → N) (mp : Nat) (a : Option Nat) (n : Nat) :
    Nat × Nat :=
  allocaShape lay ρ (.ptr mp) 1 a n

/-- The value that units of the memory `ρ n` decode to as a pointer of
memory `M`, `M = mp`, in that memory's byte order, as a result vector. -/
abbrev loadPtrResult (lay : N → MemLayout) (ρ : Mem → N) (mp n : Nat)
    (us : List (MemUnit (lay (ρ n)).unit)) : HVector toType [Ty.ptr mp] :=
  .cons (decodePtr mp (ptrShape lay ρ mp none n).1 (lay (ρ n)).order us : PoisonOr Pointer) .nil

/-- The units that a value of `ptr<M>`, `M = mp`, takes in the memory
`ρ n`: its encoding in that memory's byte order. -/
abbrev storePtrUnits (lay : N → MemLayout) (ρ : Mem → N) (mp n : Nat) (v : PoisonOr Pointer) :
    List (MemUnit (lay (ρ n)).unit) :=
  encodePtr mp (ptrShape lay ρ mp none n).1 (lay (ρ n)).order v

/-- The rule of `loadPtr o mp a n`, in a monad with UB and the memory
effect on the memories of a run whose layout entries are `lay`, where the
run names the core's memory `x` as `ρ x`: UB on a poison pointer, and
otherwise the aligned load of the units of `ptr<M>` from the memory `ρ n`,
decoded as a pointer of memory `M`. -/
def loadPtrRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m] (mp : Nat)
    (a : Option Nat) (n : Nat) : PoisonOr Pointer → m (HVector toType [Ty.ptr mp])
  | .poison => MonadUB.ub poisonPointer
  | .value p => loadPtrResult lay ρ mp n <$> MonadMemory.load (unit := unitsOf lay) (m := m)
      (ρ n) p (ptrShape lay ρ mp a n).1 (ptrShape lay ρ mp a n).2

/-- The rule of `storePtr o mp a n`, in a monad with UB and the memory
effect on the memories of a run whose layout entries are `lay`, where the
run names the core's memory `x` as `ρ x`: UB on a poison pointer, and
otherwise the aligned store of the encoding of the value, a pointer of
memory `M`, to the memory `ρ n`, with no result. -/
def storePtrRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m] (mp : Nat)
    (a : Option Nat) (n : Nat) :
    PoisonOr Pointer → PoisonOr Pointer → m (HVector toType ([] : List Ty))
  | _, .poison => MonadUB.ub poisonStorePointer
  | v, .value p => (fun _ => .nil) <$> MonadMemory.store (unit := unitsOf lay) (m := m)
      (ρ n) p (storePtrUnits lay ρ mp n v) (ptrShape lay ρ mp a n).2

/-- The alignment does not change how many units a pointer access takes. -/
theorem ptrShape_fst (lay : N → MemLayout) (ρ : Mem → N) (mp : Nat) (a : Option Nat) (n : Nat) :
    (ptrShape lay ρ mp a n).1 = (ptrShape lay ρ mp none n).1 :=
  rfl

/-- In memory 0, a pointer of memory 0 takes 8 units aligned to 8, and its
encoding is its eight fragments; poison is eight poison units. -/
example : ptrShape (fun _ : Unit => MemLayout.default) (fun _ => ()) 0 none 0 = (8, 8) ∧
    storePtrUnits (fun _ : Unit => MemLayout.default) (fun _ => ()) 0 0 (.value ⟨some 0, 4⟩) =
      (List.range 8).map (.frag 0 ⟨some 0, 4⟩) ∧
    storePtrUnits (fun _ : Unit => MemLayout.default) (fun _ => ()) 0 0 .poison =
      List.replicate 8 .poison := by
  decide +kernel

end Fir.Core
