import Fir.Execution.MemoryExposeLaws
import Fir.Memory.ResolverLaws

/-!
# Turning integers into pointers in the state layer

The memory effect's turning of an integer back into a pointer, in the state
layer over the set monad, has one outcome from any memories, under any
address resolver: the pointer, with the memories in which one more call is
counted. So:

* it always has an outcome, has finitely many, and never ends in UB;
* it writes no unit of any memory, keeps the kind, alignment, size and
  liveness of every allocation and the frames, and gives no address;
* it reads no memory but its own;
* from memories that refine others it gives the same pointer, and memories
  that refine the others'.

What it changes is the count of calls, which the resolver sees. Keeping the
count is its own property, _counts no rebuild_: on each path that ends, the
count is what it was. A computation with no memory counts none, and
mapping results and sequencing keep it. Allocating, freeing, loading,
storing and exposing count none. The effect obligations do not see the
count. Which declared effect covers turning an integer back into a pointer
comes with the op that does it.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {α : Type}

local notation "SM" => StateT (Memories Mem unit) SetM

/-- The computation `c` counts no integer turned back into a pointer: on
each path that ends, the count is what it was. -/
def RebuildsNot (c : StateT (Memories Mem unit) SetM α) : Prop :=
  ∀ S a S', c S (.ok (a, S')) → S'.rebuilds = S.rebuilds

section

variable {β : Type}

omit [DecidableEq Mem] in
/-- A computation with no memory counts no rebuild. -/
theorem rebuildsNot_lift (c : SetM α) : RebuildsNot (Mem := Mem) (unit := unit) (StateT.lift c) := by
  intro S a S' h
  rcases (SetM.lift_apply c S _).1 h with ⟨_, -, he⟩ | ⟨_, -, he⟩ <;> cases he
  rfl

omit [DecidableEq Mem] in
/-- Mapping the results keeps a computation that counts no rebuild. -/
theorem RebuildsNot.map {c : StateT (Memories Mem unit) SetM α} (f : α → β)
    (h : RebuildsNot c) : RebuildsNot (f <$> c) := by
  intro S b S' hc
  rcases (SetM.stateMap_apply f c S _).1 hc with ⟨a, S'', hc, he⟩ | ⟨_, -, he⟩ <;> cases he
  exact h S a S' hc

omit [DecidableEq Mem] in
/-- A sequence counts no rebuild when its parts count none. -/
theorem RebuildsNot.bind {c : StateT (Memories Mem unit) SetM α}
    {f : α → StateT (Memories Mem unit) SetM β} (hc : RebuildsNot c)
    (hf : ∀ a, RebuildsNot (f a)) : RebuildsNot (c >>= f) := by
  intro S b S' h
  rcases (SetM.stateBind_apply c f S _).1 h with ⟨a, S₁, hc', hf'⟩ | ⟨_, _, he⟩
  · exact (hf a S₁ b S' hf').trans (hc S a S₁ hc')
  · cases he

end

variable (x : Mem) (k : Resolver) (P : Nat) (i : BitVec P)

/-- The one way turning an integer back into a pointer may end: with the
pointer and the memories it gives. -/
theorem fromAddr_apply (S : Memories Mem unit) (e : Ev (Pointer × Memories Mem unit)) :
    MonadMemory.fromAddr (m := SM) x k P i S e ↔ e = .ok (S.fromAddr x k P i) := Iff.rfl

/-- Turning an integer back into a pointer always has an outcome. -/
theorem fromAddr_hasOutcome : HasOutcome (MonadMemory.fromAddr (m := SM) x k P i) :=
  fun S => ⟨_, (fromAddr_apply x k P i S _).2 rfl⟩

/-- Turning an integer back into a pointer has one outcome. -/
theorem fromAddr_finitelyMany : FinitelyMany (MonadMemory.fromAddr (m := SM) x k P i) := fun S =>
  ⟨[S.fromAddr x k P i], fun r hr => by cases (fromAddr_apply x k P i S _).1 hr; simp⟩

/-- Turning an integer back into a pointer never ends in UB. -/
theorem fromAddr_noUB : NoUB (MonadMemory.fromAddr (m := SM) x k P i) :=
  fun S r h => by cases (fromAddr_apply x k P i S _).1 h

/-- Turning an integer back into a pointer keeps every memory and the
frames. -/
theorem fromAddr_keeps {S S' : Memories Mem unit} {p : Pointer}
    (h : MonadMemory.fromAddr (m := SM) x k P i S (.ok (p, S'))) :
    S'.mem = S.mem ∧ S'.frames = S.frames := by
  cases (fromAddr_apply x k P i S _).1 h
  exact ⟨rfl, rfl⟩

/-- Turning an integer back into a pointer writes no unit of any memory. -/
theorem fromAddr_writesNot (y : Mem) : WritesNot y (MonadMemory.fromAddr (m := SM) x k P i) :=
  fun _ _ _ h => (fromAddr_keeps x k P i h).1 ▸ List.prefix_refl _

/-- Turning an integer back into a pointer neither allocates nor frees in
any memory. -/
theorem fromAddr_allocatesNot (y : Mem) :
    AllocatesNot y (MonadMemory.fromAddr (m := SM) x k P i) := fun _ _ _ h => by
  obtain ⟨hm, hf⟩ := fromAddr_keeps x k P i h
  refine ⟨by rw [hm], ?_⟩
  unfold Memories.framesOf
  rw [hf]

/-- Turning an integer back into a pointer gives no address in any
memory. -/
theorem fromAddr_exposesNot (y : Mem) : ExposesNot y (MonadMemory.fromAddr (m := SM) x k P i) :=
  fun _ _ _ h b => by rw [(fromAddr_keeps x k P i h).1]

/-- Turning an integer back into a pointer does not read another memory:
replacing it changes neither the pointer nor the count. -/
theorem fromAddr_readsNot_ne {y : Mem} (hy : x ≠ y) :
    ReadsNot y (MonadMemory.fromAddr (m := SM) x k P i) := by
  intro S m hm e he
  cases (fromAddr_apply x k P i S _).1 he
  have hp := Memories.fromAddr_transfer (S := S) (T := S.set y m)
    (Memories.set_mem_ne _ _ (Ne.symm hy)) rfl k P i
  refine ⟨_, (fromAddr_apply x k P i _ _).2 rfl, ?_⟩
  refine ⟨hp.symm, ⟨rfl, fun z hz => ?_, ?_⟩, fun _ _ => .inr ⟨rfl, ?_⟩⟩
  · show S.mem z = (S.set y m).mem z
    rw [Memories.set_mem_ne _ _ (Ne.symm hz)]
  · show (S.mem y).allocs = ((S.set y m).mem y).allocs
    rw [Memories.set_mem_self, hm]
  · show ((S.set y m).mem y).unitAt _ _ = _
    rw [Memories.set_mem_self]

/-- Turning an integer back into a pointer in memories that refine others
gives the same pointer, and memories that refine the others'. -/
theorem fromAddr_refines :
    StateRefinedBy Eq (MonadMemory.fromAddr (m := SM) x k P i) (MonadMemory.fromAddr x k P i) := by
  intro S S' hS e he
  cases (fromAddr_apply x k P i S' _).1 he
  exact ⟨_, (fromAddr_apply x k P i S _).2 rfl, Memories.IsRefinedBy.fromAddr hS x k P i⟩

/-- Turning an integer back into a pointer counts the call. -/
theorem fromAddr_counts {S S' : Memories Mem unit} {p : Pointer}
    (h : MonadMemory.fromAddr (m := SM) x k P i S (.ok (p, S'))) : S'.rebuilds = S.rebuilds + 1 := by
  cases (fromAddr_apply x k P i S _).1 h
  rfl

/-! # Ops that count no rebuild -/

/-- An allocation counts no rebuild. -/
theorem alloc_rebuildsNot (kd : AllocKind) (n al : Nat) :
    RebuildsNot (MonadMemory.alloc (m := SM) x kd n al) := by
  intro S _ S' h
  cases h
  show (S.alloc x kd n al).2.rebuilds = _
  unfold Memories.alloc
  dsimp only
  split
  · unfold Memories.record
    split <;> rfl
  · rfl

/-- Freeing counts no rebuild. -/
theorem free_rebuildsNot (a : AllocId) : RebuildsNot (MonadMemory.free (m := SM) x a) := by
  intro S _ S' h
  cases h
  rfl

/-- A load counts no rebuild. -/
theorem load_rebuildsNot (p : Pointer) (n al : Nat) :
    RebuildsNot (MonadMemory.load (m := SM) x p n al) := by
  intro S _ S' h
  rw [load_keeps x p n al h]

/-- A store counts no rebuild. -/
theorem store_rebuildsNot (p : Pointer) (us : List (MemUnit (unit x))) (al : Nat) :
    RebuildsNot (MonadMemory.store (m := SM) x p us al) := by
  intro S _ S' h
  rcases (store_apply x p us al S _).1 h with ⟨S'', hs, he⟩ | ⟨_, _, he⟩ <;> cases he
  unfold Memories.store at hs
  cases hm : (S.mem x).storeAligned p us al with
  | error f => rw [hm] at hs; cases hs
  | ok N => rw [hm] at hs; cases hs; rfl

/-- An exposure counts no rebuild. -/
theorem expose_rebuildsNot (g : Policy) (p : Pointer) :
    RebuildsNot (MonadMemory.expose (m := SM) x g P p) := by
  intro S _ S' h
  rcases expose_ok x g P p h with rfl | ⟨a, z, -, rfl⟩ <;> rfl

end Fir
