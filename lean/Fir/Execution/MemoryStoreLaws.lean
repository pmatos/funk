import Fir.Execution.MemoryLoadLaws

/-!
# Stores in the state layer

The memory effect's store, in the state layer over the set monad, has one
outcome from any memories: UB, for the reason of its fault, misaligned
included, or the memories with its units written. So it meets every
obligation that an op that stores and does nothing else declares:

* it always has an outcome, and it has finitely many;
* it writes no unit of any memory but its own;
* it neither allocates nor frees in any memory: a store keeps the kind,
  alignment, size, liveness and constness of every allocation, and the
  frames;
* it reads no memory, its own included
  (`docs/decisions/semantics-effects.md#soundness`): replace a memory by
  any memory of the same allocations, and the store faults for the same
  reason, or writes the same units at the same place, leaving every other
  unit as it was in each. Whether it faults, misaligned included, depends
  on the allocations of its memory, which the replacement keeps, and not
  on their units. So a store declares a write and no read;
* to memories that refine others, a store of units that refine the others'
  faults for the same reason, or gives memories that refine the others'.

It may end in UB, so it declares may-UB. An op whose rule stores, as the
core's `store`, meets its obligations with memory from these.
-/

namespace Fir

open Memory

namespace Memory

variable {u : Nat}

/-- The unit at offset `i` of the allocation `a`, through the list's
lookups. -/
theorem Memory.unitAt_eq (M : Memory u) (a i : Nat) :
    M.unitAt a i = M.blocks[a]?.bind (·.units[i]?) := by
  simp [Memory.unitAt, List.head?_drop]

/-- Two memories of the same allocations have, at each id, blocks of the
same kind, alignment, size, liveness and constness. -/
theorem Memory.shape_getElem? {M M' : Memory u} (h : M.allocs = M'.allocs) (a : Nat) :
    (M.blocks[a]?).map Block.shape = (M'.blocks[a]?).map Block.shape := by
  have := congrArg (·[a]?) h
  simpa [Memory.allocs, List.getElem?_map] using this

/-- An access lands at the same allocation and offset, or faults for the
same reason, in two memories of the same allocations. -/
theorem Memory.locate_allocs {M M' : Memory u} (h : M.allocs = M'.allocs) (p : Pointer)
    (n : Nat) :
    (M.locate p n).map (fun r => (r.1, r.2.2)) = (M'.locate p n).map (fun r => (r.1, r.2.2)) := by
  obtain ⟨prov, off⟩ := p
  cases prov with
  | none => rfl
  | some a =>
    have k := Memory.shape_getElem? h a
    cases hb : M.blocks[a]? <;> cases hb' : M'.blocks[a]? <;>
      simp_all [Memory.locate, Block.shape] <;>
      split <;> (try split) <;> rfl

/-- A write inside a block holds the written units from its offset on, and
the block's units elsewhere. -/
theorem Block.write_getElem? (b : Block u) {o : Nat} {us : List (MemUnit u)}
    (h : o + us.length ≤ b.units.length) (i : Nat) :
    (b.write o us).units[i]? = if o ≤ i ∧ i < o + us.length then us[i - o]? else b.units[i]? := by
  simp only [Block.write, List.getElem?_append, List.length_append, List.length_take,
    List.getElem?_take, List.getElem?_drop]
  grind

/-- A store keeps a memory's allocations. -/
theorem Memory.allocs_store {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') : M'.allocs = M.allocs :=
  List.ext_getElem? fun a => by simpa [Memory.allocs, List.getElem?_map] using store_shape h a

/-- An aligned store to two memories of the same allocations faults for the
same reason in both, or writes the same units at the same place of each. -/
theorem Memory.storeAligned_allocs {M M' : Memory u} (h : M.allocs = M'.allocs) (p : Pointer)
    (us : List (MemUnit u)) (al : Nat) :
    (∃ f, M.storeAligned p us al = .error f ∧ M'.storeAligned p us al = .error f) ∨
      ∃ a b b' o, M.locate p us.length = .ok (a, b, o) ∧ M'.locate p us.length = .ok (a, b', o) ∧
        M.storeAligned p us al = .ok ⟨M.blocks.set a (b.write o us)⟩ ∧
        M'.storeAligned p us al = .ok ⟨M'.blocks.set a (b'.write o us)⟩ := by
  have hl := Memory.locate_allocs h p us.length
  have ha := Memory.aligned_of_shapes h p al
  unfold Memory.storeAligned
  rw [← ha]
  cases hs : M.locate p us.length with
  | error f =>
    cases hm : M'.locate p us.length with
    | error f' =>
      rw [hs, hm] at hl
      cases hl
      rw [store_of_locate_error hs, store_of_locate_error hm]
      exact .inl ⟨f, rfl, rfl⟩
    | ok r => rw [hs, hm] at hl; cases hl
  | ok r =>
    obtain ⟨a, b, o⟩ := r
    cases hm : M'.locate p us.length with
    | error f => rw [hs, hm] at hl; cases hl
    | ok r' =>
      obtain ⟨a', b', o'⟩ := r'
      rw [hs, hm] at hl
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have k := Memory.shape_getElem? h a
      rw [(Memory.locate_eq_ok.1 hs).2.1, (Memory.locate_eq_ok.1 hm).2.1] at k
      have hc : b'.const = b.const := by
        simp only [Option.map_some, Option.some.injEq, Block.shape, Prod.mk.injEq] at k
        exact k.2.2.2.2.symm
      cases hb : b.const
      case true =>
        rw [store_constant hs hb, store_constant hm (hc.trans hb)]
        exact .inl ⟨_, rfl, rfl⟩
      rw [store_of_locate hs hb, store_of_locate hm (hc.trans hb)]
      cases M.aligned p al
      · exact .inl ⟨_, rfl, rfl⟩
      · exact .inr ⟨a, b, b', o, rfl, rfl, rfl, rfl⟩

end Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

local notation "SM" => StateT (Memories Mem unit) SetM

variable (x : Mem) (p : Pointer) (us : List (MemUnit (unit x))) (al : Nat)

/-- The ways a store may end: with the memories it gives, or in UB for the
reason of its fault. -/
theorem store_apply (S : Memories Mem unit) (e : Ev (Unit × Memories Mem unit)) :
    MonadMemory.store (m := SM) x p us al S e ↔
      (∃ S', S.store x p us al = .ok S' ∧ e = .ok ((), S')) ∨
        ∃ f, S.store x p us al = .error f ∧ e = .ub f.reason := by
  show (match S.store x p us al with
    | .ok S' => (pure ((), S') : SetM _)
    | .error f => MonadUB.ub f.reason) e ↔ _
  cases S.store x p us al with
  | ok S' =>
    exact ⟨fun h => .inl ⟨S', rfl, h⟩, by rintro (⟨_, ⟨⟩, rfl⟩ | ⟨_, ⟨⟩, _⟩); rfl⟩
  | error f =>
    exact ⟨fun h => .inr ⟨f, rfl, h⟩, by rintro (⟨_, ⟨⟩, _⟩ | ⟨_, ⟨⟩, rfl⟩); rfl⟩

/-- A store that ends replaces its own memory by one of the same
allocations, and changes nothing else. -/
theorem store_ok {S S' : Memories Mem unit} (h : S.store x p us al = .ok S') :
    ∃ N, S' = S.set x N ∧ N.allocs = (S.mem x).allocs := by
  unfold Memories.store at h
  cases hs : (S.mem x).storeAligned p us al with
  | error f => rw [hs] at h; cases h
  | ok N =>
    rw [hs] at h
    cases h
    exact ⟨N, rfl, Memory.allocs_store (Memory.storeAligned_eq_ok.1 hs).1⟩

/-- A store always has an outcome. -/
theorem store_hasOutcome : HasOutcome (MonadMemory.store (m := SM) x p us al) := fun S => by
  cases h : S.store x p us al with
  | ok S' => exact ⟨_, (store_apply x p us al S _).2 (.inl ⟨S', h, rfl⟩)⟩
  | error f => exact ⟨_, (store_apply x p us al S _).2 (.inr ⟨f, h, rfl⟩)⟩

/-- A store has at most one outcome that ends. -/
theorem store_finitelyMany : FinitelyMany (MonadMemory.store (m := SM) x p us al) := fun S => by
  refine ⟨match S.store x p us al with
    | .ok S' => [((), S')]
    | .error _ => [], fun r hr => ?_⟩
  rcases (store_apply x p us al S _).1 hr with ⟨S', h, he⟩ | ⟨_, _, he⟩ <;> cases he
  simp [h]

/-- A store writes no unit of any memory but its own. -/
theorem store_writesNot {y : Mem} (hy : x ≠ y) :
    WritesNot y (MonadMemory.store (m := SM) x p us al) := by
  intro S _ S' h
  rcases (store_apply x p us al S _).1 h with ⟨_, h, he⟩ | ⟨_, _, he⟩ <;> cases he
  obtain ⟨N, rfl, -⟩ := store_ok x p us al h
  rw [Memories.set_mem_ne _ _ hy]
  exact prefix_refl _

/-- A store neither allocates nor frees in any memory. -/
theorem store_allocatesNot (y : Mem) : AllocatesNot y (MonadMemory.store (m := SM) x p us al) := by
  intro S _ S' h
  rcases (store_apply x p us al S _).1 h with ⟨_, h, he⟩ | ⟨_, _, he⟩ <;> cases he
  obtain ⟨N, rfl, hN⟩ := store_ok x p us al h
  refine ⟨?_, rfl⟩
  by_cases hy : x = y
  · subst hy
    rw [Memories.set_mem_self, hN]
  · rw [Memories.set_mem_ne _ _ hy]

/-- A store does not read another memory: replacing it changes neither
what the store writes nor whether it faults. -/
theorem store_readsNot_ne {y : Mem} (hy : x ≠ y) :
    ReadsNot y (MonadMemory.store (m := SM) x p us al) := by
  intro S m hm e he
  have hx : (S.set y m).mem x = S.mem x := Memories.set_mem_ne _ _ (Ne.symm hy)
  rcases (store_apply x p us al S _).1 he with ⟨_, h, rfl⟩ | ⟨f, h, rfl⟩
  · unfold Memories.store at h
    cases hs : (S.mem x).storeAligned p us al with
    | error f => rw [hs] at h; cases h
    | ok N =>
      rw [hs] at h
      cases h
      have h' : (S.set y m).store x p us al = .ok ((S.set y m).set x N) := by
        simp only [Memories.store, hx, hs, Except.map]
      refine ⟨_, (store_apply x p us al _ _).2 (.inl ⟨_, h', rfl⟩), rfl,
        ⟨rfl, fun z hz => ?_, ?_⟩, fun b i => .inr ⟨?_, ?_⟩⟩
      · by_cases hzx : x = z
        · subst hzx
          rw [Memories.set_mem_self, Memories.set_mem_self]
        · rw [Memories.set_mem_ne _ _ hzx, Memories.set_mem_ne _ _ hzx,
            Memories.set_mem_ne _ _ (Ne.symm hz)]
      · rw [Memories.set_mem_ne _ _ hy, Memories.set_mem_ne _ _ hy, Memories.set_mem_self, hm]
      · rw [Memories.set_mem_ne _ _ hy]
      · rw [Memories.set_mem_ne _ _ hy, Memories.set_mem_self]
  · refine ⟨_, (store_apply x p us al _ _).2 (.inr ⟨f, ?_, rfl⟩), rfl⟩
    simp only [Memories.store, hx] at h ⊢
    cases hs : (S.mem x).storeAligned p us al <;> rw [hs] at h <;> cases h
    rfl

/-- A store does not read its own memory: replace it by any memory of the
same allocations, and the store faults for the same reason, or writes the
same units at the same place, leaving every other unit as it was in
each. -/
theorem store_readsNot_self : ReadsNot x (MonadMemory.store (m := SM) x p us al) := by
  intro S m hm e he
  rcases Memory.storeAligned_allocs hm.symm p us al with ⟨f, h₁, h₂⟩ |
    ⟨a, b, b', o, hs, hm', h₁, h₂⟩
  · rcases (store_apply x p us al S _).1 he with ⟨_, h, rfl⟩ | ⟨f', h, rfl⟩ <;>
      simp only [Memories.store, h₁, Except.map] at h <;> cases h
    refine ⟨_, (store_apply x p us al _ _).2 (.inr ⟨f, ?_, rfl⟩), rfl⟩
    simp only [Memories.store, Memories.set_mem_self, h₂, Except.map]
  · rcases (store_apply x p us al S _).1 he with ⟨_, h, rfl⟩ | ⟨f', h, rfl⟩ <;>
      simp only [Memories.store, h₁, Except.map] at h <;> cases h
    have h' : (S.set x m).store x p us al = .ok ((S.set x m).set x ⟨m.blocks.set a (b'.write o us)⟩) :=
      by simp only [Memories.store, Memories.set_mem_self, h₂, Except.map]
    refine ⟨_, (store_apply x p us al _ _).2 (.inl ⟨_, h', rfl⟩), rfl,
      ⟨rfl, fun z hz => ?_, ?_⟩, fun c i => ?_⟩
    · rw [Memories.set_mem_ne _ _ (Ne.symm hz), Memories.set_mem_ne _ _ (Ne.symm hz),
        Memories.set_mem_ne _ _ (Ne.symm hz)]
    · obtain ⟨-, hb, -, h0, hn, rfl⟩ := Memory.locate_eq_ok.1 hs
      obtain ⟨-, hb', -, -, hn', -⟩ := Memory.locate_eq_ok.1 hm'
      have k := Memory.shape_getElem? hm a
      rw [hb, hb'] at k
      simp only [Option.map_some, Option.some.injEq, Block.shape, Prod.mk.injEq] at k
      simp only [Memories.set_mem_self, Memory.allocs, List.map_set]
      rw [← Memory.allocs, ← Memory.allocs, hm]
      simp only [Block.shape, Block.write, List.length_append, List.length_take,
        List.length_drop]
      congr 1
      simp only [Prod.mk.injEq]
      refine ⟨k.1.symm, k.2.1.symm, by omega, k.2.2.2.1.symm, k.2.2.2.2.symm⟩
    · obtain ⟨-, hb, -, h0, hn, rfl⟩ := Memory.locate_eq_ok.1 hs
      obtain ⟨-, hb', -, -, hn', -⟩ := Memory.locate_eq_ok.1 hm'
      simp only [Memories.set_mem_self, Memory.unitAt_eq, List.getElem?_set]
      by_cases hc : a = c
      · subst hc
        rw [hb, hb']
        have hlen : a < (S.mem x).blocks.length := (List.getElem?_eq_some_iff.1 hb).1
        have hlen' : a < m.blocks.length := (List.getElem?_eq_some_iff.1 hb').1
        simp only [hlen, hlen', ite_true, Option.bind_some]
        rw [Block.write_getElem? b (o := p.offset.toNat) (us := us) (by omega),
          Block.write_getElem? b' (o := p.offset.toNat) (us := us) (by omega)]
        split
        · exact .inl rfl
        · exact .inr ⟨rfl, rfl⟩
      · simp only [hc, ite_false]
        exact .inr ⟨trivial, trivial⟩

/-- A store reads no memory, its own included. -/
theorem store_readsNot (y : Mem) : ReadsNot y (MonadMemory.store (m := SM) x p us al) := by
  by_cases hy : x = y
  · subst hy
    exact store_readsNot_self x p us al
  · exact store_readsNot_ne x p us al hy

/-- A store, to memories that refine others, of units that refine the
others' faults for the same reason, or gives memories that refine the
others'. -/
theorem store_refines {us us' : List (MemUnit (unit x))} (hu : us ⊑ us') :
    StateRefinedBy Eq (MonadMemory.store (m := SM) x p us al) (MonadMemory.store x p us' al) := by
  intro S S' hS e he
  rcases hS.store x p hu al with ⟨f, h₁, h₂⟩ | ⟨T, T', h₁, h₂, hT⟩
  · exact ⟨_, (store_apply x p us al S _).2 (.inr ⟨f, h₁, rfl⟩), trivial⟩
  · rcases (store_apply x p us' al S' _).1 he with ⟨_, h, rfl⟩ | ⟨_, h, rfl⟩ <;> rw [h₂] at h <;>
      cases h
    exact ⟨_, (store_apply x p us al S _).2 (.inl ⟨T, h₁, rfl⟩), rfl, hT⟩

end Fir
