import Fir

/-!
A store does not read its memory
(`docs/decisions/semantics-effects.md#soundness`): replace the memory
by any memory of the same allocations, and the store faults for the same
reason or writes the same units at the same place, leaving every other unit
as it was in each. So a dialect may declare a store with a write and no
read. This is the case that shapes the obligation _no read_: whether a
store faults depends on the allocations of its memory, which the
replacement keeps, and not on their units.
-/

namespace FirTest.MemoryStoreReads

open Fir Fir.Memory

variable {u : Nat}

/-- The unit at offset `i` of the allocation `a`, through the list's
lookups. -/
theorem unitAt_eq (M : Memory u) (a i : Nat) :
    M.unitAt a i = M.blocks[a]?.bind (·.units[i]?) := by
  simp [Memory.unitAt, List.head?_drop]

/-- Two memories of the same allocations have, at each id, blocks of the
same kind, alignment, size and liveness. -/
theorem shape_getElem? {M M' : Memory u} (h : M.allocs = M'.allocs) (a : Nat) :
    (M.blocks[a]?).map Block.shape = (M'.blocks[a]?).map Block.shape := by
  have := congrArg (·[a]?) h
  simpa [Memory.allocs, List.getElem?_map] using this

/-- An access lands at the same allocation and offset, or faults for the
same reason, in two memories of the same allocations. -/
theorem locate_allocs {M M' : Memory u} (h : M.allocs = M'.allocs) (p : Pointer) (n : Nat) :
    (M.locate p n).map (fun r => (r.1, r.2.2)) = (M'.locate p n).map (fun r => (r.1, r.2.2)) := by
  obtain ⟨prov, off⟩ := p
  cases prov with
  | none => rfl
  | some a =>
    have k := shape_getElem? h a
    cases hb : M.blocks[a]? <;> cases hb' : M'.blocks[a]? <;>
      simp_all [Memory.locate, Block.shape] <;>
      split <;> (try split) <;> rfl

/-- A write inside a block holds the written units from its offset on, and
the block's units elsewhere. -/
theorem write_getElem? (b : Memory.Block u) {o : Nat} {us : List (MemUnit u)}
    (h : o + us.length ≤ b.units.length) (i : Nat) :
    (b.write o us).units[i]? = if o ≤ i ∧ i < o + us.length then us[i - o]? else b.units[i]? := by
  simp only [Memory.Block.write, List.getElem?_append, List.length_append, List.length_take,
    List.getElem?_take, List.getElem?_drop]
  grind

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A store does not read its memory. -/
theorem store_readsNot (x : Mem) (p : Pointer) (us : List (MemUnit (unit x))) :
    ReadsNot x (MonadMemory.store (m := StateT (Memories Mem unit) SetM) x p us) := by
  intro S m hm e he
  have hl := locate_allocs hm.symm p us.length
  simp only [MonadMemory.store, Memories.store, Memories.set_mem_self] at he ⊢
  cases hs : (S.mem x).locate p us.length with
  | error f =>
    cases hm' : m.locate p us.length with
    | error f' =>
      rw [hs, hm'] at hl
      cases hl
      rw [Memory.store_eq_error.2 hs] at he
      rw [Memory.store_eq_error.2 hm']
      exact ⟨e, he, by cases he; rfl⟩
    | ok r => rw [hs, hm'] at hl; cases hl
  | ok r =>
    obtain ⟨a, b, o⟩ := r
    cases hm' : m.locate p us.length with
    | error f => rw [hs, hm'] at hl; cases hl
    | ok r' =>
      obtain ⟨a', b', o'⟩ := r'
      rw [hs, hm'] at hl
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [Memory.store_of_locate hs] at he
      rw [Memory.store_of_locate hm']
      obtain rfl : e = .ok ((), S.set x ⟨(S.mem x).blocks.set a (b.write o us)⟩) := he
      refine ⟨_, rfl, rfl, ⟨rfl, fun y hy => ?_, ?_⟩, fun c i => ?_⟩
      · rw [Memories.set_mem_ne _ _ (Ne.symm hy), Memories.set_mem_ne _ _ (Ne.symm hy),
          Memories.set_mem_ne _ _ (Ne.symm hy)]
      · obtain ⟨-, hb, -, h0, hn, rfl⟩ := Memory.locate_eq_ok.1 hs
        obtain ⟨-, hb', -, -, hn', -⟩ := Memory.locate_eq_ok.1 hm'
        have k := shape_getElem? hm a
        rw [hb, hb'] at k
        simp only [Option.map_some, Option.some.injEq, Block.shape, Prod.mk.injEq] at k
        simp only [Memories.set_mem_self, Memory.allocs, List.map_set]
        rw [← Memory.allocs, ← Memory.allocs, hm]
        simp only [Block.shape, Memory.Block.write, List.length_append, List.length_take,
          List.length_drop]
        congr 1
        simp only [Prod.mk.injEq]
        refine ⟨k.1.symm, k.2.1.symm, by omega, k.2.2.2.symm⟩
      · obtain ⟨-, hb, -, h0, hn, rfl⟩ := Memory.locate_eq_ok.1 hs
        obtain ⟨-, hb', -, -, hn', -⟩ := Memory.locate_eq_ok.1 hm'
        simp only [Memories.set_mem_self, unitAt_eq, List.getElem?_set]
        by_cases hc : a = c
        · subst hc
          rw [hb, hb']
          have hlen : a < (S.mem x).blocks.length := (List.getElem?_eq_some_iff.1 hb).1
          have hlen' : a < m.blocks.length := (List.getElem?_eq_some_iff.1 hb').1
          simp only [hlen, hlen', ite_true, Option.bind_some]
          rw [write_getElem? b (o := p.offset.toNat) (us := us) (by omega),
            write_getElem? b' (o := p.offset.toNat) (us := us) (by omega)]
          split
          · exact .inl rfl
          · exact .inr ⟨rfl, rfl⟩
        · simp only [hc, ite_false]
          exact .inr ⟨trivial, trivial⟩

end FirTest.MemoryStoreReads
