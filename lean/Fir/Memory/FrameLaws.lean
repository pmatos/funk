import Fir.Memory.Frames
import Fir.Memory.Laws

/-!
# Frame laws

The laws below say what entering and leaving a call do to the memories of a
run, and what they leave alone:

* Entering a call and leaving it at once changes nothing.
* Allocating on the stack records the allocation in the innermost frame; an
  allocation of another kind is in no frame. An allocation in one memory
  leaves every other memory as it was.
* Leaving a call frees exactly the allocations of its frame. Every other
  allocation, of any memory, keeps its kind, its units and its liveness, and
  no memory gains or loses an allocation.
* So a stack allocation that a call makes is freed when the call returns,
  and every access to it after that is UB (ADR-2026-11-09-1548).
-/

namespace Fir.Memory

namespace Memories

variable {Mem : Type} {unit : Mem → Nat}

/-!
# Replacing one memory
-/

variable [DecidableEq Mem]

/-- Entering a call changes no memory. -/
theorem enter_mem (S : Memories Mem unit) : S.enter.mem = S.mem := rfl

/-- Entering a call and leaving it at once changes nothing. -/
theorem exit_enter (S : Memories Mem unit) : S.enter.exit = S := rfl

/-- Every memory of the empty memories is empty. -/
@[simp] theorem empty_mem (x : Mem) : (empty : Memories Mem unit).mem x = .empty := rfl

/-- Dropping the entries of the name `x` from a table leaves the memory of
every other name as it was. -/
theorem lookup_filter {x y : Mem} (h : x ≠ y) :
    ∀ t : List (Σ z : Mem, Memory (unit z)),
      lookup y (t.filter fun e => !decide (e.1 = x)) = lookup y t
  | [] => rfl
  | ⟨z, m⟩ :: t => by
    show lookup y (match !decide (z = x) with
        | true => ⟨z, m⟩ :: t.filter _ | false => t.filter _) = _
    cases hd : decide (z = x) with
    | true =>
      have hz : z ≠ y := fun e => h ((of_decide_eq_true hd).symm.trans e)
      show _ = if hz : z = y then hz ▸ m else lookup y t
      rw [dite_eq_right hz]
      exact lookup_filter h t
    | false =>
      show (if hz : z = y then hz ▸ m else lookup y (t.filter _)) = _
      rw [lookup_filter h t]
      rfl

/-- The memory that is replaced is the new one. This and the next are proved
without axioms, as the memory obligations of the test dialects need. -/
@[simp] theorem set_mem_self (S : Memories Mem unit) (x : Mem) (m : Memory (unit x)) :
    (S.set x m).mem x = m :=
  dite_eq_left rfl

/-- Every other memory stays as it was. -/
theorem set_mem_ne (S : Memories Mem unit) {x y : Mem} (m : Memory (unit x)) (h : x ≠ y) :
    (S.set x m).mem y = S.mem y :=
  (dite_eq_right h).trans (lookup_filter h S.table)

/-- Replacing a memory keeps the frames. -/
@[simp] theorem set_frames (S : Memories Mem unit) (x : Mem) (m : Memory (unit x)) :
    (S.set x m).frames = S.frames := rfl

/-!
# Freeing
-/

/-- Freeing a freed block changes nothing. -/
theorem kill_kill {u : Nat} (b : Block u) : b.kill.kill = b.kill := rfl

/-- A free changes only the allocation it frees, which it kills. -/
theorem free_get (S : Memories Mem unit) (y : Mem) (b : AllocId) (x : Mem) (a : AllocId) :
    ((S.free y b).mem x).blocks[a]? =
      if (y, b) = (x, a) then ((S.mem x).blocks[a]?).map Block.kill
      else (S.mem x).blocks[a]? := by
  by_cases hy : y = x
  · subst hy
    by_cases hb : b = a
    · subst hb
      simp [free, Memory.free]
    · simp [free, Memory.free_blocks_ne _ hb, hb]
  · simp [free, set_mem_ne _ _ hy, hy]

/-- A free keeps the number of allocations of every memory. -/
theorem free_length (S : Memories Mem unit) (y : Mem) (b : AllocId) (x : Mem) :
    ((S.free y b).mem x).blocks.length = (S.mem x).blocks.length := by
  by_cases hy : y = x
  · subst hy
    simp [free, Memory.free]
  · simp [free, set_mem_ne _ _ hy]

/-- Freeing a list kills the allocations it lists, and leaves every other
allocation as it was. -/
theorem freeAll_get (x : Mem) (a : AllocId) : ∀ (S : Memories Mem unit) (l : List (Mem × AllocId)),
    ((S.freeAll l).mem x).blocks[a]? =
      if (x, a) ∈ l then ((S.mem x).blocks[a]?).map Block.kill else (S.mem x).blocks[a]?
  | S, [] => by simp [freeAll]
  | S, (y, b) :: l => by
    rw [freeAll, freeAll_get x a (S.free y b) l, free_get]
    by_cases h : (y, b) = (x, a)
    · cases h
      by_cases hl : (x, a) ∈ l <;> simp [hl, Option.map_map, Function.comp_def, kill_kill]
    · by_cases hl : (x, a) ∈ l
      · simp [h, hl]
      · simp only [h, hl, ite_false, List.mem_cons, Ne.symm h, false_or]

/-- Freeing a list keeps the number of allocations of every memory. -/
theorem freeAll_length (x : Mem) : ∀ (S : Memories Mem unit) (l : List (Mem × AllocId)),
    ((S.freeAll l).mem x).blocks.length = (S.mem x).blocks.length
  | _, [] => rfl
  | S, (y, b) :: l => by rw [freeAll, freeAll_length x _ l, free_length]

/-- Freeing a list keeps the frames. -/
theorem freeAll_frames : ∀ (S : Memories Mem unit) (l : List (Mem × AllocId)),
    (S.freeAll l).frames = S.frames
  | _, [] => rfl
  | S, (_, _) :: l => by rw [freeAll, freeAll_frames _ l]; rfl

/-!
# Leaving a call
-/

/-- Leaving a call pops its frame. -/
theorem exit_frames {S : Memories Mem unit} {fr : List (Mem × AllocId)}
    {frs : List (List (Mem × AllocId))} (h : S.frames = fr :: frs) : S.exit.frames = frs := by
  simp only [exit, h, freeAll_frames]

/-- Leaving a call frees exactly the allocations of its frame: it kills
each of them, and leaves every other allocation as it was. -/
theorem exit_get {S : Memories Mem unit} {fr : List (Mem × AllocId)}
    {frs : List (List (Mem × AllocId))} (h : S.frames = fr :: frs) (x : Mem) (a : AllocId) :
    (S.exit.mem x).blocks[a]? =
      if (x, a) ∈ fr then ((S.mem x).blocks[a]?).map Block.kill else (S.mem x).blocks[a]? := by
  simp only [exit, h]
  exact freeAll_get x a _ fr

/-- Leaving a call keeps the number of allocations of every memory. -/
theorem exit_length (S : Memories Mem unit) (x : Mem) :
    (S.exit.mem x).blocks.length = (S.mem x).blocks.length := by
  unfold exit
  split
  · rfl
  · exact freeAll_length x _ _

/-!
# Allocating
-/

/-- Recording an allocation changes no memory. -/
theorem record_mem (S : Memories Mem unit) (x : Mem) (a : AllocId) :
    (S.record x a).mem = S.mem := by
  unfold record
  split <;> rfl

/-- An allocation gives the pointer that its memory's allocation gives. -/
theorem alloc_fst (S : Memories Mem unit) (x : Mem) (k : AllocKind) (n : Nat) :
    (S.alloc x k n).1 = ⟨some (S.mem x).blocks.length, 0⟩ := rfl

/-- An allocation allocates in its own memory. -/
theorem alloc_mem_self (S : Memories Mem unit) (x : Mem) (k : AllocKind) (n : Nat) :
    (S.alloc x k n).2.mem x = ((S.mem x).alloc k n).2 := by
  by_cases hk : k = .stack <;> simp [alloc, hk, record_mem]

/-- An allocation leaves every other memory as it was. -/
theorem alloc_mem_ne (S : Memories Mem unit) {x y : Mem} (k : AllocKind) (n : Nat) (h : x ≠ y) :
    (S.alloc x k n).2.mem y = S.mem y := by
  by_cases hk : k = .stack <;> simp [alloc, hk, record_mem, set_mem_ne _ _ h]

/-- A stack allocation is recorded in the innermost frame. -/
theorem alloc_stack_frames {S : Memories Mem unit} {fr : List (Mem × AllocId)}
    {frs : List (List (Mem × AllocId))} (h : S.frames = fr :: frs) (x : Mem) (n : Nat) :
    (S.alloc x .stack n).2.frames = ((x, (S.mem x).blocks.length) :: fr) :: frs := by
  simp [alloc, record, h]

/-- An allocation of another kind is in no frame. -/
theorem alloc_frames {k : AllocKind} (hk : k ≠ .stack) (S : Memories Mem unit) (x : Mem)
    (n : Nat) : (S.alloc x k n).2.frames = S.frames := by
  simp [alloc, hk]

/-!
# A call's stack allocation
-/

/-- A stack allocation that a call makes is freed when the call returns. -/
theorem enter_alloc_exit (S : Memories Mem unit) (x : Mem) (n : Nat) :
    (((S.enter.alloc x .stack n).2.exit).mem x).blocks[(S.mem x).blocks.length]? =
      some ⟨.stack, List.replicate n .poison, false⟩ := by
  have hf : (S.enter.alloc x .stack n).2.frames = [(x, (S.mem x).blocks.length)] :: S.frames :=
    alloc_stack_frames (S := S.enter) rfl x n
  rw [exit_get hf]
  simp [alloc_mem_self, enter_mem, Memory.alloc_blocks_new, Block.kill]

/-- Every access to a call's stack allocation after the call returns is
UB. -/
theorem enter_alloc_exit_load (S : Memories Mem unit) (x : Mem) (n : Nat) (off : Int)
    (k : Nat) :
    ((S.enter.alloc x .stack n).2.exit).load x ⟨some (S.mem x).blocks.length, off⟩ k =
      .error .freed :=
  Memory.load_eq_error.2 (Memory.locate_freed (enter_alloc_exit S x n) rfl off k)

end Memories

end Fir.Memory
