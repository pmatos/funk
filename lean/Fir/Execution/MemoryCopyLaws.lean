import Fir.Execution.MemoryBindLaws
import Fir.Execution.MemoryLoadLaws
import Fir.Execution.MemoryStoreLaws

/-!
# Copies of units in the state layer

Copying and moving memory carry each unit across exactly: bits, poison and
pointer fragments alike, so that a copied pointer keeps its provenance
(ADR-2026-11-09-1551). The step they share is a _copy of units_: a load of
`n` units of one memory through the source pointer, then a store of the
same units through the destination pointer, in the same memory. The load
leaves the memories as they were, so the store sees what the copy started
from, and a copy whose ranges overlap writes what the source held before
the copy began, as a move must.

A copy of units is an access through both pointers, so it faults as they
do, whatever `n` is: through a pointer with no provenance or into a freed
allocation, it faults even for `n = 0`. Whether the ops that copy and move
memory reach it for a zero length, and what they check before it, such as
an overlap of their ranges, is for their rules to decide (#234); this
section proves what the copy of units does on its own.

In the state layer over the set monad a copy of units has one outcome from
any memories: UB, for the reason of the load's fault or the store's, or
the memories that the store gives. So it meets every obligation of an op
that reads and writes one memory and does nothing else:

* it always has an outcome, and it has finitely many;
* it writes no unit of any other memory, and neither allocates nor frees in
  any memory, its own included;
* it reads no other memory: from memories in which another memory is
  replaced by one of the same allocations, it faults for the same reason
  or writes the same units at the same place;
* from memories that refine others, it faults for the same reason, or
  gives memories that refine the others'.

Each but the third follows from the load's and the store's, through the
laws of sequences of the previous section. It may end in UB, so it
declares may-UB. It reads and writes its own memory, so no obligation asks
that it not read or write that one.
-/

namespace Fir

open Memory

namespace Memory.Memories

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Copies `n` units of the memory `x` from `src` to `dst`: loads them
through `src`, an access aligned to `al` units, then stores them through
`dst`, aligned to `al'`, or gives the fault of the load or of the store. -/
def copy (S : Memories Mem unit) (x : Mem) (dst src : Pointer) (n al al' : Nat) :
    Except Fault (Memories Mem unit) :=
  (S.load x src n al).bind fun us => S.store x dst us al'

end Memory.Memories

/-- A copy of units, in a monad with the memory effect: loads `n` units of
the memory `x` through `src`, aligned to `al` units, then stores them
through `dst`, aligned to `al'`. -/
def copyUnits {Mem : Type} {unit : Mem → Nat} {m : Type → Type} [Monad m]
    [MonadMemory Mem unit m] (x : Mem) (dst src : Pointer) (n al al' : Nat) : m Unit :=
  MonadMemory.load x src n al >>= fun us => MonadMemory.store x dst us al'

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

local notation "SM" => StateT (Memories Mem unit) SetM

variable (x : Mem) (dst src : Pointer) (n al al' : Nat)

/-- The ways a copy of units may end: as the store of the units the load
gives, when the load gives units, or in UB for the reason of the load's
fault. -/
theorem copyUnits_load (S : Memories Mem unit) (e : Ev (Unit × Memories Mem unit)) :
    copyUnits (m := SM) x dst src n al al' S e ↔
      (∃ us, S.load x src n al = .ok us ∧ MonadMemory.store (m := SM) x dst us al' S e) ∨
        ∃ f, S.load x src n al = .error f ∧ e = .ub f.reason := by
  rw [copyUnits, SetM.stateBind_apply]
  constructor
  · rintro (⟨us, S₁, hl, hs⟩ | ⟨r, hl, rfl⟩)
    · rcases (load_apply x src n al S _).1 hl with ⟨_, h, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact .inl ⟨us, h, hs⟩
    · rcases (load_apply x src n al S _).1 hl with ⟨_, _, he⟩ | ⟨f, h, he⟩ <;> cases he
      exact .inr ⟨f, h, rfl⟩
  · rintro (⟨us, h, hs⟩ | ⟨f, h, rfl⟩)
    · exact .inl ⟨us, S, (load_apply x src n al S _).2 (.inl ⟨us, h, rfl⟩), hs⟩
    · exact .inr ⟨_, (load_apply x src n al S _).2 (.inr ⟨f, h, rfl⟩), rfl⟩

/-- The ways a copy of units may end: with the memories that the copy
gives, or in UB for the reason of its fault. -/
theorem copyUnits_apply (S : Memories Mem unit) (e : Ev (Unit × Memories Mem unit)) :
    copyUnits (m := SM) x dst src n al al' S e ↔
      (∃ S', S.copy x dst src n al al' = .ok S' ∧ e = .ok ((), S')) ∨
        ∃ f, S.copy x dst src n al al' = .error f ∧ e = .ub f.reason := by
  rw [copyUnits_load]
  unfold Memories.copy
  cases hl : S.load x src n al with
  | error f =>
    simp only [Except.bind, reduceCtorEq, false_and, exists_false, Except.error.injEq,
      exists_eq_left', false_or]
  | ok us =>
    simp only [Except.bind, Except.ok.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false]
    exact store_apply x dst us al' S e

/-- A copy of units always has an outcome. -/
theorem copyUnits_hasOutcome : HasOutcome (copyUnits (m := SM) x dst src n al al') :=
  (load_hasOutcome x src n al).bind fun us => store_hasOutcome x dst us al'

/-- A copy of units has at most one outcome that ends. -/
theorem copyUnits_finitelyMany : FinitelyMany (copyUnits (m := SM) x dst src n al al') :=
  (load_finitelyMany x src n al).bind fun us => store_finitelyMany x dst us al'

/-- A copy of units writes no unit of any memory but its own. -/
theorem copyUnits_writesNot {y : Mem} (hy : x ≠ y) :
    WritesNot y (copyUnits (m := SM) x dst src n al al') :=
  (load_writesNot x src n al y).bind fun us => store_writesNot x dst us al' hy

/-- A copy of units neither allocates nor frees in any memory, its own
included. -/
theorem copyUnits_allocatesNot (y : Mem) :
    AllocatesNot y (copyUnits (m := SM) x dst src n al al') :=
  (load_allocatesNot x src n al y).bind fun us => store_allocatesNot x dst us al' y

/-- A copy of units does not read another memory: replacing it changes
neither what the copy loads nor what its store does. -/
theorem copyUnits_readsNot {y : Mem} (hy : x ≠ y) :
    ReadsNot y (copyUnits (m := SM) x dst src n al al') := by
  intro S m hm e he
  have hl : (S.set y m).load x src n al = S.load x src n al := by
    simp only [Memories.load, Memories.set_mem_ne _ _ (Ne.symm hy)]
  rcases (copyUnits_load x dst src n al al' S e).1 he with ⟨us, h, hs⟩ | ⟨f, h, rfl⟩
  · obtain ⟨e', hs', hm'⟩ := store_readsNot_ne x dst us al' hy S m hm e hs
    exact ⟨e', (copyUnits_load x dst src n al al' _ e').2 (.inl ⟨us, hl.trans h, hs'⟩), hm'⟩
  · exact ⟨_, (copyUnits_load x dst src n al al' _ _).2 (.inr ⟨f, hl.trans h, rfl⟩), rfl⟩

/-- A copy of units from memories that refine others faults for the same
reason, or gives memories that refine the others'. -/
theorem copyUnits_refines :
    StateRefinedBy Eq (copyUnits (m := SM) x dst src n al al')
      (copyUnits x dst src n al al') :=
  (load_refines x src n al).bind fun _ _ hu => store_refines x dst al' hu

end Fir
