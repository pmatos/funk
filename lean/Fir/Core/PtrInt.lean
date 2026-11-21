import Fir.Core.Store

/-!
# Rules of pointers as integers

This section gives `ptrExpose` and `ptrFromInt` their rules (#232;
ADR-2026-11-09-1542). Each works in the memory `N` of its pointer, whose
pointers are `P` bits wide in the module's data layout, and reads the
run's address policy or resolver for memory `N` from the items that the
run gives each op (the section on the items a run gives each op).

`ptr_expose`, `ptrExpose n w`, turns a pointer into an `iW`:

* on a defined pointer it is the memory effect's exposure under the run's
  address policy: the allocation's address plus the pointer's offset,
  wrapped at `P` bits, where an allocation with no address is given one.
  When no address may be given, it is immediate UB (the human's ruling of
  2026-11-18 on #232, Q5);
* a poison pointer is immediate UB. Exposing a defined pointer may give
  its allocation an address, and memories that refine others have the
  same addresses, so a poison result that left the memories as they were
  would not be refined by the run on a pointer in its place. The op's
  poison class is an exception for that reason (the section on the poison
  classes of the core ops).

`ptr_from_int`, `ptrFromInt n w`, turns an `iW` back into a pointer:

* on a defined integer it is the memory effect's turning of the integer
  back into a pointer under the run's resolver: of a live, exposed
  allocation that holds the address, the end included, or with no
  provenance when none does (the human's rulings of 2026-11-18, Q3, and
  of 2026-11-20, question A). It is never UB;
* a poison integer gives a poison pointer, and counts the call as a
  defined integer does: memories that refine others count as many calls,
  so a run on a poison integer must count it too to be refined by a run on
  a value in its place. The integer it counts the call with, `0`, is never
  the address of an allocation.

The integer is as wide as the memory's pointers in every valid module
(the human's ruling of 2026-11-18 on #232, Q2): the module's data layout
checks it. `fir-ref run` runs a module without validating it, so the rules
are total: an integer of another width is cut or padded with zeros to the
pointer width, and the address to the op's width.

The rules need the memory effect and the run's items, so `ptrExpose` and
`ptrFromInt` have no rule in the set monad (the section on the core's
rules with memory).
-/

namespace Fir.Core

open Memory

/-- Why exposing a poison pointer is UB. -/
def poisonExposePointer : String := "a ptr_expose of a poison pointer"

variable {N : Type} {m : Type → Type} [Monad m] [MonadUB m]

/-- The rule of `ptrExpose n w` on the pointer `p`, in a monad with UB and
the memory effect on the memories of a run whose layout entries are `lay`,
where the run names the core's memory `x` as `ρ x` and gives the items `L`:
UB on a poison pointer, and otherwise the exposure of the pointer in the
memory `ρ n`, under the run's address policy for memory `n`, at its
entry's pointer width, as an `iW`. -/
def ptrExposeRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (L : RunItems) (n w : Nat) : PoisonOr Pointer → m (HVector toType [Ty.int w])
  | .value p => (fun a => .cons (.value (a.setWidth w)) .nil) <$>
      MonadMemory.expose (unit := unitsOf lay) (ρ n) (L.addrs n) (lay (ρ n)).pointer p
  | .poison => MonadUB.ub poisonExposePointer

/-- The rule of `ptrFromInt n w` on the integer `i`, in a monad with the
memory effect: the pointer that the integer, at the pointer width of the
memory `ρ n`'s entry, turns back into under the run's resolver for memory
`n`, and for poison, poison, counting the call all the same. -/
def ptrFromIntRule (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) m]
    (L : RunItems) (n w : Nat) : PoisonOr (BitVec w) → m (HVector toType [Ty.ptr n])
  | .value i => (fun p => .cons (.value p) .nil) <$>
      MonadMemory.fromAddr (unit := unitsOf lay) (ρ n) (L.resolvers n) (lay (ρ n)).pointer
        (i.setWidth _)
  | .poison => (fun _ => .cons .poison .nil) <$>
      MonadMemory.fromAddr (unit := unitsOf lay) (ρ n) (L.resolvers n) (lay (ρ n)).pointer 0

/-- A morphism that keeps UB and exposing maps the rule of `ptrExpose` in
the one monad to the same rule in the other. -/
theorem ptrExposeRule_map {μ ν : Type → Type} [Monad μ] [Monad ν] [MonadUB μ] [MonadUB ν]
    (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) μ]
    [MonadMemory N (unitsOf lay) ν] (φ : MonadMorphism μ ν)
    (hu : ∀ {α : Type} (r : String), φ.map (MonadUB.ub r : μ α) = MonadUB.ub r)
    (he : ∀ x g P p, φ.map (MonadMemory.expose (m := μ) x g P p) = MonadMemory.expose x g P p)
    (L : RunItems) (n w : Nat) (p : PoisonOr Pointer) :
    φ.map (ptrExposeRule (m := μ) lay ρ L n w p) = ptrExposeRule lay ρ L n w p := by
  cases p with
  | value q => exact (φ.map_map _ _).trans (congrArg _ (he _ _ _ _))
  | poison => exact hu _

/-- A morphism that keeps turning integers back into pointers maps the rule
of `ptrFromInt` in the one monad to the same rule in the other. -/
theorem ptrFromIntRule_map {μ ν : Type → Type} [Monad μ] [Monad ν]
    (lay : N → MemLayout) (ρ : Mem → N) [MonadMemory N (unitsOf lay) μ]
    [MonadMemory N (unitsOf lay) ν] (φ : MonadMorphism μ ν)
    (hf : ∀ x k P i, φ.map (MonadMemory.fromAddr (m := μ) x k P i) = MonadMemory.fromAddr x k P i)
    (L : RunItems) (n w : Nat) (i : PoisonOr (BitVec w)) :
    φ.map (ptrFromIntRule (m := μ) lay ρ L n w i) = ptrFromIntRule lay ρ L n w i := by
  cases i <;> exact (φ.map_map _ _).trans (congrArg _ (hf _ _ _ _))

end Fir.Core
