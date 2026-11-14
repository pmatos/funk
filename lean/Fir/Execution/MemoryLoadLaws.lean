import Fir.Execution.MemoryObligationLaws
import Fir.Execution.MemoryTotal
import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryOpRefine

/-!
# Loads in the state layer

The memory effect's load, in the state layer over the set monad, has one
outcome from any memories: UB, for the reason of its fault, misaligned
included, or the units it loads, with the memories as they were. So it
meets every obligation that an op that loads and does nothing else
declares:

* it always has an outcome, and it has finitely many;
* it writes no unit of any memory, and neither allocates nor frees in any
  memory: a path that ends keeps the memories;
* it reads no memory but its own: from memories in which another memory is
  replaced by one of the same allocations, it faults for the same reason or
  loads the same units, and the memories it ends with are the memories it
  started from in each run;
* from memories that refine others, it faults for the same reason, or
  loads units that refine the others'.

It may end in UB, so it declares may-UB. An op whose rule loads, as the
core's `load`, meets its obligations with memory from these, through the
laws that mapping its results keeps them.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

local notation "SM" => StateT (Memories Mem unit) SetM

variable (x : Mem) (p : Pointer) (n al : Nat)

/-- The ways a load may end: with the units it loads and the memories as
they were, or in UB for the reason of its fault. -/
theorem load_apply (S : Memories Mem unit) (e : Ev (List (MemUnit (unit x)) × Memories Mem unit)) :
    MonadMemory.load (m := SM) x p n al S e ↔
      (∃ us, S.load x p n al = .ok us ∧ e = .ok (us, S)) ∨
        ∃ f, S.load x p n al = .error f ∧ e = .ub f.reason := by
  show (match S.load x p n al with
    | .ok us => (pure (us, S) : SetM _)
    | .error f => MonadUB.ub f.reason) e ↔ _
  cases S.load x p n al with
  | ok us =>
    exact ⟨fun h => .inl ⟨us, rfl, h⟩, by rintro (⟨_, ⟨⟩, rfl⟩ | ⟨_, ⟨⟩, _⟩); rfl⟩
  | error f =>
    exact ⟨fun h => .inr ⟨f, rfl, h⟩, by rintro (⟨_, ⟨⟩, _⟩ | ⟨_, ⟨⟩, rfl⟩); rfl⟩

/-- A load that ends keeps the memories. -/
theorem load_keeps {S S' : Memories Mem unit} {us : List (MemUnit (unit x))}
    (h : MonadMemory.load (m := SM) x p n al S (.ok (us, S'))) : S' = S := by
  rcases (load_apply x p n al S _).1 h with ⟨_, _, he⟩ | ⟨_, _, he⟩ <;> cases he
  rfl

/-- A load always has an outcome. -/
theorem load_hasOutcome : HasOutcome (MonadMemory.load (m := SM) x p n al) := fun S => by
  cases h : S.load x p n al with
  | ok us => exact ⟨_, (load_apply x p n al S _).2 (.inl ⟨us, h, rfl⟩)⟩
  | error f => exact ⟨_, (load_apply x p n al S _).2 (.inr ⟨f, h, rfl⟩)⟩

/-- A load has at most one outcome that ends. -/
theorem load_finitelyMany : FinitelyMany (MonadMemory.load (m := SM) x p n al) := fun S => by
  refine ⟨match S.load x p n al with
    | .ok us => [(us, S)]
    | .error _ => [], fun r hr => ?_⟩
  rcases (load_apply x p n al S _).1 hr with ⟨us, h, he⟩ | ⟨_, _, he⟩ <;> cases he
  simp [h]

/-- A load writes no unit of any memory. -/
theorem load_writesNot (y : Mem) : WritesNot y (MonadMemory.load (m := SM) x p n al) :=
  fun _ _ _ h => load_keeps x p n al h ▸ prefix_refl _

/-- A load neither allocates nor frees in any memory. -/
theorem load_allocatesNot (y : Mem) : AllocatesNot y (MonadMemory.load (m := SM) x p n al) :=
  fun _ _ _ h => load_keeps x p n al h ▸ ⟨rfl, rfl⟩

/-- A load reads no memory but its own: replacing another memory changes
neither what it loads nor whether it faults. -/
theorem load_readsNot {y : Mem} (hy : x ≠ y) :
    ReadsNot y (MonadMemory.load (m := SM) x p n al) := by
  intro S m hm e he
  have hl : (S.set y m).load x p n al = S.load x p n al := by
    simp only [Memories.load, Memories.set_mem_ne _ _ (Ne.symm hy)]
  rcases (load_apply x p n al S _).1 he with ⟨us, h, rfl⟩ | ⟨f, h, rfl⟩
  · refine ⟨_, (load_apply x p n al _ _).2 (.inl ⟨us, hl.trans h, rfl⟩), rfl,
      ⟨rfl, fun z hz => (Memories.set_mem_ne _ _ (Ne.symm hz)).symm, ?_⟩, fun b i => ?_⟩
    · rw [Memories.set_mem_self, hm]
    · exact .inr ⟨rfl, by rw [Memories.set_mem_self]⟩
  · exact ⟨_, (load_apply x p n al _ _).2 (.inr ⟨f, hl.trans h, rfl⟩), rfl⟩

/-- A load from memories that refine others faults for the same reason, or
loads units that refine the others', with the memories it started from. -/
theorem load_refines :
    StateRefinedBy (· ⊑ ·) (MonadMemory.load (m := SM) x p n al) (MonadMemory.load x p n al) := by
  intro S S' hS e he
  rcases hS.load x p n al with ⟨f, h₁, h₂⟩ | ⟨us, us', h₁, h₂, hu⟩
  · exact ⟨_, (load_apply x p n al S _).2 (.inr ⟨f, h₁, rfl⟩), trivial⟩
  · rcases (load_apply x p n al S' _).1 he with ⟨_, h, rfl⟩ | ⟨_, h, rfl⟩ <;> rw [h₂] at h <;>
      cases h
    exact ⟨_, (load_apply x p n al S _).2 (.inl ⟨us, h₁, rfl⟩), hu, hS⟩

end Fir
