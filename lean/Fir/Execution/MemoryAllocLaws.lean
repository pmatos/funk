import Fir.Execution.MemoryObligationLaws
import Fir.Execution.MemoryTotal
import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryOpRefine

/-!
# Allocation in the state layer

The memory effect's allocation, in the state layer over the set monad, has
one outcome from any memories: the pointer to a new allocation of the
memory it names, and the memories with that allocation. So it meets every
obligation an op that allocates and does nothing else declares:

* it never ends in UB, it always has an outcome, and it has finitely many;
* it writes no unit of any memory: each allocation that was there keeps its
  units, and the new one follows them;
* it reads no memory: from memories in which a memory is replaced by one of
  the same allocations, it allocates at the same place, and the memories it
  ends with agree off that memory, whose old units are as each run had them
  and whose new allocation is the same in both;
* it allocates in no memory but its own: every other memory keeps its
  allocations, and the frames keep its stack allocations;
* from memories that refine others it gives the same pointer, and memories
  that refine the others'.

An op whose rule allocates, as the core's `alloca`, meets its obligations
with memory from these, through the laws that mapping its results keeps
them.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

local notation "SM" => StateT (Memories Mem unit) SetM

namespace Memory

variable {u : Nat}

/-- An allocation keeps the units of every allocation that was there. -/
theorem Memory.unitAt_alloc_lt (M : Memory u) (k : AllocKind) (n al : Nat) {a : AllocId}
    (h : a < M.blocks.length) (i : Nat) : (M.alloc k n al).2.unitAt a i = M.unitAt a i := by
  simp [Memory.unitAt, Memory.alloc, List.drop_append_of_le_length (Nat.le_of_lt h),
    List.head?_append, List.head?_drop, List.getElem?_eq_getElem h]

/-- Past the allocations that were there, an allocation's units depend on
how many there were, and on nothing else of the memory. -/
theorem Memory.unitAt_alloc_ge {M M' : Memory u} (hl : M.blocks.length = M'.blocks.length)
    (k : AllocKind) (n al : Nat) {a : AllocId} (h : M.blocks.length ≤ a) (i : Nat) :
    (M.alloc k n al).2.unitAt a i = (M'.alloc k n al).2.unitAt a i := by
  simp [Memory.unitAt, Memory.alloc, List.drop_append, List.drop_eq_nil_of_le h,
    List.drop_eq_nil_of_le (hl ▸ h), hl]

/-- An allocation adds the new block's shape to the allocations. -/
theorem Memory.allocs_alloc (M : Memory u) (k : AllocKind) (n al : Nat) :
    (M.alloc k n al).2.allocs = M.allocs ++ [(k, al, n, true)] := by
  simp [Memory.allocs, Memory.alloc, Block.shape]

/-- Memories of the same allocations have as many blocks. -/
theorem Memory.length_of_allocs {M M' : Memory u} (h : M.allocs = M'.allocs) :
    M.blocks.length = M'.blocks.length := by
  simpa [Memory.allocs] using congrArg List.length h

end Memory

variable (x : Mem) (k : AllocKind) (n al : Nat)

/-- An allocation never ends in UB. -/
theorem alloc_noUB : NoUB (MonadMemory.alloc (m := SM) x k n al) := fun _ _ h => by cases h

/-- An allocation always has an outcome. -/
theorem alloc_hasOutcome : HasOutcome (MonadMemory.alloc (m := SM) x k n al) :=
  fun S => ⟨.ok (S.alloc x k n al), rfl⟩

/-- An allocation has one outcome. -/
theorem alloc_finitelyMany : FinitelyMany (MonadMemory.alloc (m := SM) x k n al) :=
  fun S => ⟨[S.alloc x k n al], fun _ h => by cases h; exact List.mem_singleton_self _⟩

/-- An allocation writes no unit of any memory: the new allocation follows
the ones that were there. -/
theorem alloc_writesNot (y : Mem) : WritesNot y (MonadMemory.alloc (m := SM) x k n al) := by
  intro S _ _ h
  cases h
  by_cases hx : x = y
  · subst hx
    show (S.mem x).contents <+: ((S.alloc x k n al).2.mem x).contents
    rw [Memories.alloc_mem_self]
    exact ⟨[List.replicate n .poison], by simp [Memory.contents, Memory.alloc]⟩
  · show (S.mem y).contents <+: ((S.alloc x k n al).2.mem y).contents
    rw [Memories.alloc_mem_ne _ _ _ _ hx]
    exact prefix_refl _

/-- The frames after an allocation in `x` list the same stack allocations
of every other memory. -/
theorem framesOf_alloc_ne (S : Memories Mem unit) {y : Mem} (h : x ≠ y) :
    (S.alloc x k n al).2.framesOf y = S.framesOf y := by
  by_cases hk : k = .stack
  · subst hk
    cases hf : S.frames with
    | nil => simp [Memories.framesOf, Memories.alloc, Memories.record, hf]
    | cons fr frs =>
      simp [Memories.framesOf, Memories.alloc_stack_frames hf, hf, h]
  · simp [Memories.framesOf, Memories.alloc_frames hk]

/-- An allocation in `x` allocates in no other memory. -/
theorem alloc_allocatesNot {y : Mem} (h : x ≠ y) :
    AllocatesNot y (MonadMemory.alloc (m := SM) x k n al) := by
  intro S _ _ he
  cases he
  exact ⟨congrArg Memory.allocs (Memories.alloc_mem_ne _ _ _ _ h), framesOf_alloc_ne x k n al S h⟩

/-- An allocation reads no memory: from memories in which `y` is replaced
by a memory of the same allocations, it gives the same pointer, and
memories that agree off `y`, whose units of `y` are each the same, or as
each run had them. -/
theorem alloc_readsNot (y : Mem) : ReadsNot y (MonadMemory.alloc (m := SM) x k n al) := by
  intro S m hm e he
  cases he
  have hl := Memory.length_of_allocs hm
  refine ⟨.ok ((S.set y m).alloc x k n al), rfl, ?_, ?_, ?_⟩
  · by_cases hx : x = y
    · subst hx
      simp [Memories.alloc_fst, hl]
    · simp [Memories.alloc_fst, Memories.set_mem_ne _ _ (Ne.symm hx)]
  · refine ⟨?_, fun z hz => ?_, ?_⟩
    · by_cases hx : x = y
      · subst hx
        by_cases hk : k = .stack <;> cases hf : S.frames <;>
          simp [Memories.alloc, Memories.record, hk, hl, hf]
      · by_cases hk : k = .stack <;> cases hf : S.frames <;>
          simp [Memories.alloc, Memories.record, hk, hf, Memories.set_mem_ne _ _ (Ne.symm hx)]
    · by_cases hzx : x = z
      · subst hzx
        rw [Memories.alloc_mem_self, Memories.alloc_mem_self, Memories.set_mem_ne _ _ hz.symm]
      · rw [Memories.alloc_mem_ne _ _ _ _ hzx, Memories.alloc_mem_ne _ _ _ _ hzx,
          Memories.set_mem_ne _ _ hz.symm]
    · by_cases hx : x = y
      · subst hx
        rw [Memories.alloc_mem_self, Memories.alloc_mem_self, Memories.set_mem_self,
          Memory.allocs_alloc, Memory.allocs_alloc, hm]
      · rw [Memories.alloc_mem_ne _ _ _ _ hx, Memories.alloc_mem_ne _ _ _ _ hx,
          Memories.set_mem_self, hm]
  · intro b i
    by_cases hx : x = y
    · subst hx
      rw [Memories.alloc_mem_self, Memories.alloc_mem_self, Memories.set_mem_self]
      by_cases hb : b < (S.mem x).blocks.length
      · exact .inr ⟨Memory.unitAt_alloc_lt _ _ _ _ hb i,
          Memory.unitAt_alloc_lt _ _ _ _ (hl ▸ hb) i⟩
      · exact .inl (Memory.unitAt_alloc_ge hl.symm _ _ _ (Nat.le_of_not_lt hb) i)
    · rw [Memories.alloc_mem_ne _ _ _ _ hx, Memories.alloc_mem_ne _ _ _ _ hx,
        Memories.set_mem_self]
      exact .inr ⟨rfl, rfl⟩

/-- Allocating in memories that refine others gives the same pointer, and
memories that refine the others'. -/
theorem alloc_refines :
    StateRefinedBy Eq (MonadMemory.alloc (m := SM) x k n al) (MonadMemory.alloc x k n al) := by
  intro S S' hS e he
  cases he
  obtain ⟨hp, hm⟩ := hS.alloc x k n al
  exact ⟨.ok (S.alloc x k n al), rfl, hp, hm⟩

end Fir
