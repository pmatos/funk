import Fir.Execution.MemoryStoreLaws
import Fir.Execution.MemoryBindLaws
import Fir.Memory.PolicyLaws

/-!
# Exposing in the state layer

The memory effect's exposure, in the state layer over the set monad, has one
outcome from any memories, under any address policy: the integer of the
pointer, with the memories in which its allocation has an address, or UB
when no address may be given. So:

* it always has an outcome, and it has finitely many;
* it writes no unit of any memory, and keeps the kind, alignment, size and
  liveness of every allocation, and the frames;
* it reads no memory but its own, and gives no address in any other memory;
* from memories that refine others it gives the same integer, or UB in
  both, and memories that refine the others'.

What it changes is an address. The effect obligations compare units and
shapes, not addresses, so they cannot tell exposing from doing nothing.
Giving no allocation of a memory an address is its own property, _exposes
nothing in x_: on each path that ends, every allocation of `x` keeps its
address, and a new one has none. A computation with no memory exposes
nothing, and mapping results and sequencing keep it. Allocating, freeing,
loading and storing expose nothing in any memory, and exposing exposes
nothing in any memory but its own. Exposing counts as allocating in its
memory, as a declared effect (the human's ruling of 2026-11-20 on #232,
question B): the op that exposes declares it.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {α : Type}

local notation "SM" => StateT (Memories Mem unit) SetM

/-- The computation `c` gives no allocation of the memory `x` an address: on
each path that ends, every allocation of `x` has the address it had, and a
new one has none. -/
def ExposesNot (x : Mem) (c : StateT (Memories Mem unit) SetM α) : Prop :=
  ∀ S a S', c S (.ok (a, S')) → ∀ b, (S'.mem x).addrOf b = (S.mem x).addrOf b

section

variable {x : Mem} {β : Type}

/-- A computation with no memory exposes nothing. -/
theorem exposesNot_lift (c : SetM α) : ExposesNot (unit := unit) x (StateT.lift c) := by
  intro S a S' h b
  rcases (SetM.lift_apply c S _).1 h with ⟨_, -, he⟩ | ⟨_, -, he⟩ <;> cases he
  rfl

/-- Mapping the results keeps a computation that exposes nothing. -/
theorem ExposesNot.map {c : StateT (Memories Mem unit) SetM α} (f : α → β)
    (h : ExposesNot x c) : ExposesNot x (f <$> c) := by
  intro S b S' hc
  rcases (SetM.stateMap_apply f c S _).1 hc with ⟨a, S'', hc, he⟩ | ⟨_, -, he⟩ <;> cases he
  exact h S a S' hc

/-- A sequence exposes nothing when its parts expose nothing. -/
theorem ExposesNot.bind {c : StateT (Memories Mem unit) SetM α}
    {f : α → StateT (Memories Mem unit) SetM β} (hc : ExposesNot x c)
    (hf : ∀ a, ExposesNot x (f a)) : ExposesNot x (c >>= f) := by
  intro S b S' h a'
  rcases (SetM.stateBind_apply c f S _).1 h with ⟨a, S₁, hc', hf'⟩ | ⟨_, _, he⟩
  · exact (hf a S₁ b S' hf' a').trans (hc S a S₁ hc' a')
  · cases he

end

variable (x : Mem) (g : Policy) (P : Nat) (p : Pointer)

/-- The ways an exposure may end: with the integer and memories it gives,
or in UB when no address may be given. -/
theorem expose_apply (S : Memories Mem unit) (e : Ev (BitVec P × Memories Mem unit)) :
    MonadMemory.expose (m := SM) x g P p S e ↔
      (∃ r, S.expose x g P p = some r ∧ e = .ok r) ∨
        (S.expose x g P p = none ∧ e = .ub noAddressReason) := by
  show (match S.expose x g P p with
    | some r => (pure r : SetM _)
    | none => MonadUB.ub noAddressReason) e ↔ _
  cases S.expose x g P p with
  | some r => exact ⟨fun h => .inl ⟨r, rfl, h⟩, by rintro (⟨_, ⟨⟩, rfl⟩ | ⟨⟨⟩, _⟩); rfl⟩
  | none => exact ⟨fun h => .inr ⟨rfl, h⟩, by rintro (⟨_, ⟨⟩, _⟩ | ⟨_, rfl⟩); rfl⟩

/-- An exposure ends in UB exactly when its allocation is one of its
memory, has no address, and no address may be given to it. -/
theorem expose_ub (S : Memories Mem unit) (r : String) :
    MonadMemory.expose (m := SM) x g P p S (.ub r) ↔
      r = noAddressReason ∧ ∃ a b, p.prov = some a ∧ (S.mem x).blocks[a]? = some b ∧
        b.addr = none ∧ ∀ y, (S.mem x).admits 1 (addrHi P) a y = false := by
  rw [expose_apply, ← Memories.expose_eq_none]
  constructor
  · rintro (⟨_, _, ⟨⟩⟩ | ⟨h, ⟨⟩⟩)
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact .inr ⟨h, rfl⟩

/-- An exposure always has an outcome. -/
theorem expose_hasOutcome : HasOutcome (MonadMemory.expose (m := SM) x g P p) := fun S => by
  cases h : S.expose x g P p with
  | some r => exact ⟨_, (expose_apply x g P p S _).2 (.inl ⟨r, h, rfl⟩)⟩
  | none => exact ⟨_, (expose_apply x g P p S _).2 (.inr ⟨h, rfl⟩)⟩

/-- An exposure has at most one outcome that ends. -/
theorem expose_finitelyMany : FinitelyMany (MonadMemory.expose (m := SM) x g P p) := fun S => by
  refine ⟨(S.expose x g P p).toList, fun r hr => ?_⟩
  rcases (expose_apply x g P p S _).1 hr with ⟨r', h, he⟩ | ⟨_, he⟩ <;> cases he
  simp [h]

/-- The memories an exposure ends with: the same, or the memory `x` with
one more address. -/
theorem expose_ok {S S' : Memories Mem unit} {v : BitVec P}
    (h : MonadMemory.expose (m := SM) x g P p S (.ok (v, S'))) : S' = S ∨
      ∃ a y, (S.mem x).addrOf a = none ∧ S' = S.set x ((S.mem x).expose a y) := by
  rcases (expose_apply x g P p S _).1 h with ⟨_, h, he⟩ | ⟨_, he⟩ <;> cases he
  rcases Memories.expose_cases h with h | ⟨a, y, -, ha, -, h⟩
  · exact .inl h
  · exact .inr ⟨a, y, ha, h⟩

/-- An exposure writes no unit of any memory. -/
theorem expose_writesNot (y : Mem) : WritesNot y (MonadMemory.expose (m := SM) x g P p) := by
  intro S _ S' h
  rcases expose_ok x g P p h with rfl | ⟨a, z, -, rfl⟩
  · exact List.prefix_refl _
  · by_cases hy : x = y
    · subst hy
      rw [Memories.set_mem_self]
      unfold Memory.contents
      rw [Memory.expose_contents]
      exact List.prefix_refl _
    · rw [Memories.set_mem_ne _ _ hy]
      exact List.prefix_refl _

/-- An exposure neither allocates nor frees in any memory. -/
theorem expose_allocatesNot (y : Mem) : AllocatesNot y (MonadMemory.expose (m := SM) x g P p) := by
  intro S _ S' h
  rcases expose_ok x g P p h with rfl | ⟨a, z, -, rfl⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨?_, rfl⟩
    by_cases hy : x = y
    · subst hy
      rw [Memories.set_mem_self]
      exact Memory.expose_shapes _ a z
    · rw [Memories.set_mem_ne _ _ hy]

/-- An exposure gives no address in any memory but its own. -/
theorem expose_exposesNot {y : Mem} (hy : x ≠ y) :
    ExposesNot y (MonadMemory.expose (m := SM) x g P p) := by
  intro S _ S' h b
  rcases expose_ok x g P p h with rfl | ⟨a, z, -, rfl⟩
  · rfl
  · rw [Memories.set_mem_ne _ _ hy]

/-- Results that differ only in the memory `y`, which is in one as it was
and in the other the memory that replaced it, match. -/
theorem ReadsNot.match_ok {y : Mem} {S S₁ S₂ : Memories Mem unit} {m : Memory (unit y)}
    (hm : m.allocs = (S.mem y).allocs) (a : α) (h₁ : S₁.mem y = S.mem y) (h₂ : S₂.mem y = m)
    (hf : S₁.frames = S₂.frames) (hz : ∀ z, z ≠ y → S₁.mem z = S₂.mem z) :
    ReadsNot.Match y S m (.ok (a, S₁)) (.ok (a, S₂)) :=
  ⟨rfl, ⟨hf, hz, by rw [h₁, h₂, hm]⟩, fun _ _ => .inr ⟨by rw [h₁], by rw [h₂]⟩⟩

/-- An exposure does not read another memory: replacing it changes neither
the integer nor whether no address may be given. -/
theorem expose_readsNot_ne {y : Mem} (hy : x ≠ y) :
    ReadsNot y (MonadMemory.expose (m := SM) x g P p) := by
  intro S m hm e he
  have hx : (S.set y m).mem x = S.mem x := Memories.set_mem_ne _ _ (Ne.symm hy)
  have ht := Memories.expose_transfer hx g P p
  rcases (expose_apply x g P p S e).1 he with ⟨r, h, rfl⟩ | ⟨h, rfl⟩
  · rw [h] at ht
    cases hT : (S.set y m).expose x g P p with
    | none => rw [hT] at ht; cases ht
    | some r' =>
      rw [hT] at ht
      cases ht with
      | some hr =>
        obtain ⟨v, S₁⟩ := r
        obtain ⟨v', S₂⟩ := r'
        obtain ⟨hv, hst⟩ := hr
        dsimp only at hv hst
        subst hv
        refine ⟨.ok (v, S₂), (expose_apply x g P p _ _).2 (.inl ⟨_, hT, rfl⟩), ?_⟩
        rcases hst with ⟨rfl, rfl⟩ | ⟨M, rfl, rfl⟩
        · exact ReadsNot.match_ok hm v rfl (Memories.set_mem_self _ _ _) rfl
            fun z hz => (Memories.set_mem_ne _ _ (Ne.symm hz)).symm
        · refine ReadsNot.match_ok hm v (Memories.set_mem_ne _ _ hy)
            (by rw [Memories.set_mem_ne _ _ hy, Memories.set_mem_self]) rfl fun z hz => ?_
          by_cases hzx : x = z
          · subst hzx
            simp only [Memories.set_mem_self]
          · rw [Memories.set_mem_ne _ _ hzx, Memories.set_mem_ne _ _ hzx,
              Memories.set_mem_ne _ _ (Ne.symm hz)]
  · rw [h] at ht
    cases hT : (S.set y m).expose x g P p with
    | none => exact ⟨.ub noAddressReason, (expose_apply x g P p _ _).2 (.inr ⟨hT, rfl⟩), rfl⟩
    | some r' => rw [hT] at ht; cases ht

/-- Exposing in memories that refine others gives the same integer, or UB
in both, and memories that refine the others'. -/
theorem expose_refines :
    StateRefinedBy Eq (MonadMemory.expose (m := SM) x g P p) (MonadMemory.expose x g P p) := by
  intro S S' hS e he
  have hr := Memories.IsRefinedBy.expose hS x g P p
  rcases (expose_apply x g P p S' _).1 he with ⟨r', h', rfl⟩ | ⟨h', rfl⟩
  · cases h0 : S.expose x g P p with
    | none => rw [h0, h'] at hr; cases hr
    | some r =>
      rw [h0, h'] at hr
      cases hr with
      | some hrr => exact ⟨.ok r, (expose_apply x g P p S _).2 (.inl ⟨r, h0, rfl⟩), hrr⟩
  · cases h0 : S.expose x g P p with
    | none => exact ⟨.ub noAddressReason, (expose_apply x g P p S _).2 (.inr ⟨h0, rfl⟩), trivial⟩
    | some r => rw [h0, h'] at hr; cases hr

/-! # Ops that expose nothing -/

/-- An allocation gives no address in any memory. -/
theorem alloc_exposesNot (k : AllocKind) (n al : Nat) (y : Mem) :
    ExposesNot y (MonadMemory.alloc (m := SM) x k n al) := by
  intro S _ S' h b
  cases h
  by_cases hx : x = y
  · subst hx
    show ((S.alloc x k n al).2.mem x).addrOf b = _
    rw [Memories.alloc_mem_self]
    by_cases hb : b < (S.mem x).blocks.length
    · exact Memory.addrOf_alloc_lt _ _ _ _ hb
    · have hlen := Nat.not_lt.1 hb
      have h1 : (S.mem x).addrOf b = none := by
        simp [Memory.addrOf, List.getElem?_eq_none hlen]
      rw [h1]
      rcases Nat.eq_or_lt_of_le hlen with h | h
      · subst h
        exact Memory.addrOf_alloc_new _ _ _ _
      · simp only [Memory.addrOf, Memory.alloc]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  · show ((S.alloc x k n al).2.mem y).addrOf b = _
    rw [Memories.alloc_mem_ne _ _ _ _ hx]

/-- Freeing gives no address in any memory. -/
theorem free_exposesNot (a : AllocId) (y : Mem) :
    ExposesNot y (MonadMemory.free (m := SM) x a) := by
  intro S _ S' h b
  cases h
  show ((S.set x ((S.mem x).free a)).mem y).addrOf b = _
  by_cases hx : x = y
  · subst hx
    rw [Memories.set_mem_self, Memory.addrOf_free]
  · rw [Memories.set_mem_ne _ _ hx]

/-- A load gives no address in any memory. -/
theorem load_exposesNot (n al : Nat) (y : Mem) :
    ExposesNot y (MonadMemory.load (m := SM) x p n al) := by
  intro S _ S' h b
  rw [load_keeps x p n al h]

/-- A store gives no address in any memory. -/
theorem store_exposesNot (us : List (MemUnit (unit x))) (al : Nat) (y : Mem) :
    ExposesNot y (MonadMemory.store (m := SM) x p us al) := by
  intro S _ S' h b
  rcases (store_apply x p us al S _).1 h with ⟨S'', hs, he⟩ | ⟨_, _, he⟩ <;> cases he
  unfold Memories.store at hs
  cases hm : (S.mem x).storeAligned p us al with
  | error f => rw [hm] at hs; cases hs
  | ok N =>
    rw [hm] at hs
    cases hs
    by_cases hx : x = y
    · subst hx
      rw [Memories.set_mem_self]
      exact Memory.addrOf_store (Memory.storeAligned_eq_ok.1 hm).1 b
    · rw [Memories.set_mem_ne _ _ hx]

end Fir
