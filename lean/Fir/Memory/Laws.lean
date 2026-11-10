import Fir.Memory.Model

/-!
# Memory laws

The laws below say what the accesses of a memory do, and what they leave
alone. The ops that load, store and allocate rest their effects on them: an
op that declares no write to a memory must leave it unchanged, and one that
declares a write to it changes only what it stores (ADR-2026-11-09-1541).

* An access succeeds exactly when its pointer has provenance for a live
  allocation of the memory, and every unit it touches is inside it.
  Otherwise it is immediate UB, for the reason it fails
  (ADR-2026-11-09-1542).
* Fresh memory holds poison.
* A load after a store, of the same units through the same pointer, gives
  back what was stored.
* A store changes no other allocation, and no unit of its own allocation
  outside the units it stores. It leaves every allocation's kind, size and
  liveness as they were, so it changes which accesses succeed in no way.
* An allocation leaves every existing allocation as it was, and changes no
  access through a pointer without provenance for the new allocation. A
  free changes no other allocation.
* After a free, every access to the freed allocation is UB.
-/

namespace Fir.Memory

variable {u : Nat}

/-!
# Reading and writing a block
-/

/-- A write inside a block keeps its size. -/
theorem Block.write_length (b : Block u) {o : Nat} {us : List (MemUnit u)}
    (h : o + us.length ≤ b.units.length) : (b.write o us).units.length = b.units.length := by
  simp only [Block.write, List.length_append, List.length_take, List.length_drop]
  omega

/-- A read of the units that a write inside a block wrote gives them back. -/
theorem Block.read_write_same (b : Block u) {o : Nat} {us : List (MemUnit u)}
    (h : o + us.length ≤ b.units.length) : (b.write o us).read o us.length = us := by
  have ht : (b.units.take o).length = o := by simp only [List.length_take]; omega
  simp only [Block.read, Block.write, List.append_assoc]
  rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  simp

/-- A read of units that a write does not touch gives what it gave before. -/
theorem Block.read_write_disjoint (b : Block u) {o : Nat} {us : List (MemUnit u)}
    (h : o + us.length ≤ b.units.length) {o' n : Nat} (hd : o' + n ≤ o ∨ o + us.length ≤ o') :
    (b.write o us).read o' n = b.read o' n := by
  apply List.ext_getElem?
  intro i
  simp only [Block.read, Block.write, List.getElem?_take, List.getElem?_drop, List.append_assoc]
  split
  · rw [List.getElem?_append, List.getElem?_append]
    simp only [List.length_take, List.getElem?_take, List.getElem?_drop]
    grind
  · rfl

namespace Memory

/-!
# When an access succeeds
-/

/-- An access of `n` units through `p` succeeds exactly when `p` has
provenance for a live allocation `a`, and the units from `p`'s offset to `n`
units on are inside it. -/
theorem locate_eq_ok {M : Memory u} {p : Pointer} {n : Nat} {a : AllocId} {b : Block u}
    {o : Nat} :
    M.locate p n = .ok (a, b, o) ↔
      p.prov = some a ∧ M.blocks[a]? = some b ∧ b.live = true ∧ 0 ≤ p.offset ∧
        p.offset + n ≤ b.units.length ∧ o = p.offset.toNat := by
  unfold locate
  split
  · simp_all
  · split
    · grind
    · split
      · grind
      · split <;> grind

/-- An access through a pointer without provenance is UB. -/
theorem locate_none (M : Memory u) (off : Int) (n : Nat) :
    M.locate ⟨none, off⟩ n = .error .noProvenance := rfl

/-- An access through a pointer whose allocation the memory does not have
is UB: it has no provenance for an allocation of the memory. -/
theorem locate_unknown {M : Memory u} {a : AllocId} (hb : M.blocks[a]? = none) (off : Int)
    (n : Nat) : M.locate ⟨some a, off⟩ n = .error .noProvenance := by
  simp [locate, hb]

/-- An access to a freed allocation is UB. -/
theorem locate_freed {M : Memory u} {a : AllocId} {b : Block u} (hb : M.blocks[a]? = some b)
    (hl : b.live = false) (off : Int) (n : Nat) :
    M.locate ⟨some a, off⟩ n = .error .freed := by
  simp [locate, hb, hl]

/-- An access to a live allocation that touches a unit outside it is UB. -/
theorem locate_outOfBounds {M : Memory u} {a : AllocId} {b : Block u}
    (hb : M.blocks[a]? = some b) (hl : b.live = true) {off : Int} {n : Nat}
    (hr : ¬ (0 ≤ off ∧ off + n ≤ b.units.length)) :
    M.locate ⟨some a, off⟩ n = .error .outOfBounds := by
  simp only [locate, hb, hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr]

/-- A load faults exactly when its access does, for the same reason. -/
theorem load_eq_error {M : Memory u} {p : Pointer} {n : Nat} {f : Fault} :
    M.load p n = .error f ↔ M.locate p n = .error f := by
  unfold load
  cases M.locate p n <;> simp [bind, Except.bind, pure, Except.pure]

/-- A store faults exactly when its access does, for the same reason. -/
theorem store_eq_error {M : Memory u} {p : Pointer} {us : List (MemUnit u)} {f : Fault} :
    M.store p us = .error f ↔ M.locate p us.length = .error f := by
  unfold store
  cases M.locate p us.length <;> simp [bind, Except.bind, pure, Except.pure]

/-- A successful load gives the units of its allocation from its offset
on. -/
theorem load_of_locate {M : Memory u} {p : Pointer} {n : Nat} {a : AllocId} {b : Block u}
    {o : Nat} (h : M.locate p n = .ok (a, b, o)) : M.load p n = .ok (b.read o n) := by
  simp [load, h, bind, Except.bind, pure, Except.pure]

/-- A successful store writes its units into its own allocation. -/
theorem store_of_locate {M : Memory u} {p : Pointer} {us : List (MemUnit u)} {a : AllocId}
    {b : Block u} {o : Nat} (h : M.locate p us.length = .ok (a, b, o)) :
    M.store p us = .ok ⟨M.blocks.set a (b.write o us)⟩ := by
  simp [store, h, bind, Except.bind, pure, Except.pure]

/-- What a successful store leaves: the memory with its allocation's units
written. -/
theorem store_eq_ok {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') :
    ∃ a b o, M.locate p us.length = .ok (a, b, o) ∧ M' = ⟨M.blocks.set a (b.write o us)⟩ := by
  cases hl : M.locate p us.length with
  | error f => exact absurd (store_eq_error.2 hl) (by simp [h])
  | ok r =>
    obtain ⟨a, b, o⟩ := r
    rw [store_of_locate hl, Except.ok.injEq] at h
    exact ⟨a, b, o, rfl, h.symm⟩

/-!
# Allocation
-/

/-- The pointer that an allocation gives has provenance for the new
allocation, which no allocation had before, and points at its first unit. -/
theorem alloc_fst (M : Memory u) (k : AllocKind) (n : Nat) :
    (M.alloc k n).1 = ⟨some M.blocks.length, 0⟩ := rfl

/-- An allocation leaves every existing allocation as it was. -/
theorem alloc_blocks_lt (M : Memory u) (k : AllocKind) (n : Nat) {a : AllocId}
    (ha : a < M.blocks.length) : (M.alloc k n).2.blocks[a]? = M.blocks[a]? := by
  simp [alloc, List.getElem?_append_left ha]

/-- An allocation adds one live block of its kind, of poison units. -/
theorem alloc_blocks_new (M : Memory u) (k : AllocKind) (n : Nat) :
    (M.alloc k n).2.blocks[M.blocks.length]? = some ⟨k, List.replicate n .poison, true⟩ := by
  simp [alloc]

/-- An allocation changes no access through a pointer without provenance
for the new allocation: it lands where it landed before, in the same block,
or fails for the same reason. -/
theorem locate_alloc (M : Memory u) (k : AllocKind) (size : Nat) {p : Pointer}
    (hp : p.prov ≠ some M.blocks.length) (n : Nat) :
    (M.alloc k size).2.locate p n = M.locate p n := by
  obtain ⟨prov, off⟩ := p
  cases prov with
  | none => rfl
  | some a =>
    have ha : a ≠ M.blocks.length := fun e => hp (by simp [e])
    have hb : (M.alloc k size).2.blocks[a]? = M.blocks[a]? := by
      rcases Nat.lt_or_gt_of_ne ha with h | h
      · exact alloc_blocks_lt M k size h
      · rw [List.getElem?_eq_none (by simp [alloc]; omega),
          List.getElem?_eq_none (by omega)]
    simp only [locate, hb]

/-- Fresh memory holds poison: a load of `n` units in bounds of a new
allocation gives `n` poisons. -/
theorem load_alloc (M : Memory u) (k : AllocKind) {size : Nat} {off : Int} {n : Nat}
    (h0 : 0 ≤ off) (hn : off + n ≤ size) :
    (M.alloc k size).2.load ⟨some M.blocks.length, off⟩ n = .ok (List.replicate n .poison) := by
  rw [load_of_locate (locate_eq_ok.2 ⟨rfl, alloc_blocks_new M k size, rfl, h0, by simpa using hn,
    rfl⟩)]
  simp only [Block.read, List.drop_replicate, List.take_replicate, Except.ok.injEq]
  congr 1
  omega

/-!
# Loads and stores
-/

/-- A store changes no allocation but its own. -/
theorem store_blocks_ne {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') {a : AllocId} (ha : p.prov ≠ some a) :
    M'.blocks[a]? = M.blocks[a]? := by
  obtain ⟨a', b, o, hl, rfl⟩ := store_eq_ok h
  obtain ⟨hp, -⟩ := locate_eq_ok.1 hl
  have : a' ≠ a := fun e => ha (e ▸ hp)
  simp [List.getElem?_set_ne this]

/-- A store keeps the kind, size and liveness of every allocation. -/
theorem store_shape {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') (a : AllocId) :
    (M'.blocks[a]?).map (fun b => (b.kind, b.units.length, b.live)) =
      (M.blocks[a]?).map (fun b => (b.kind, b.units.length, b.live)) := by
  obtain ⟨a', b, o, hl, rfl⟩ := store_eq_ok h
  obtain ⟨-, hb, -, h0, hn, rfl⟩ := locate_eq_ok.1 hl
  by_cases e : a' = a
  · subst e
    have hlen : a' < M.blocks.length := (List.getElem?_eq_some_iff.1 hb).1
    rw [List.getElem?_set_self hlen, hb]
    simp only [Option.map_some, Block.write_length b (by omega : p.offset.toNat + us.length ≤ _)]
    rfl
  · simp [List.getElem?_set_ne e]

/-- A store changes which accesses succeed in no way: an access after it
lands where it landed before, or fails for the same reason. -/
theorem locate_store {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') (q : Pointer) (n : Nat) :
    (M'.locate q n).map (fun r => (r.1, r.2.2)) = (M.locate q n).map (fun r => (r.1, r.2.2)) := by
  obtain ⟨prov, off⟩ := q
  cases prov with
  | none => rfl
  | some a =>
    have hs := store_shape h a
    simp only [locate]
    cases h1 : M'.blocks[a]? <;> cases h2 : M.blocks[a]? <;> simp_all [Except.map] <;>
      grind

/-- A load after a store, of the same units through the same pointer, gives
back what was stored. -/
theorem load_store_same {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') : M'.load p us.length = .ok us := by
  obtain ⟨a, b, o, hl, rfl⟩ := store_eq_ok h
  obtain ⟨hp, hb, hlive, h0, hn, rfl⟩ := locate_eq_ok.1 hl
  have hlen : a < M.blocks.length := (List.getElem?_eq_some_iff.1 hb).1
  have hfit : p.offset.toNat + us.length ≤ b.units.length := by omega
  rw [load_of_locate (b := b.write p.offset.toNat us) (locate_eq_ok.2 ⟨hp,
    List.getElem?_set_self hlen, hlive, h0, by rw [Block.write_length b hfit]; exact hn, rfl⟩),
    Block.read_write_same b hfit]

/-- A store leaves a load through a pointer into another allocation as it
was. -/
theorem load_store_ne {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') {q : Pointer} (hq : q.prov ≠ p.prov) (n : Nat) :
    M'.load q n = M.load q n := by
  obtain ⟨prov, off⟩ := q
  cases prov with
  | none => rfl
  | some a =>
    have hb := store_blocks_ne h (a := a) (fun e => hq e.symm)
    simp [load, locate, hb]

/-- A store leaves a load of units of its own allocation that it does not
store to as it was. -/
theorem load_store_disjoint {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') {q : Pointer} (hq : q.prov = p.prov) {n : Nat}
    (hd : q.offset + n ≤ p.offset ∨ p.offset + us.length ≤ q.offset) :
    M'.load q n = M.load q n := by
  have hs := locate_store h q n
  cases hq' : M.locate q n with
  | error f =>
    rw [hq'] at hs
    cases hm : M'.locate q n with
    | error f' =>
      rw [hm] at hs
      cases hs
      rw [load_eq_error.2 hm, load_eq_error.2 hq']
    | ok r => rw [hm] at hs; cases hs
  | ok r =>
    obtain ⟨a', b', o'⟩ := r
    obtain ⟨a, b, o, hl, rfl⟩ := store_eq_ok h
    obtain ⟨hp, hb, hlive, h0, hn, rfl⟩ := locate_eq_ok.1 hl
    obtain ⟨hp', hb', -, h0', hn', rfl⟩ := locate_eq_ok.1 hq'
    have ha : a' = a := Option.some.inj (hp'.symm.trans (hq.trans hp))
    subst ha
    have hbb : b' = b := Option.some.inj (hb'.symm.trans hb)
    subst hbb
    have hlen : a' < M.blocks.length := (List.getElem?_eq_some_iff.1 hb).1
    have hfit : p.offset.toNat + us.length ≤ b'.units.length := by omega
    rw [load_of_locate hq', load_of_locate (b := b'.write p.offset.toNat us) (locate_eq_ok.2
      ⟨hp', List.getElem?_set_self hlen, hlive, h0', by rw [Block.write_length b' hfit]; exact hn',
      rfl⟩), Block.read_write_disjoint b' hfit (by omega)]

/-!
# Freeing
-/

/-- A free changes no allocation but the one it frees. -/
theorem free_blocks_ne (M : Memory u) {a a' : AllocId} (h : a ≠ a') :
    (M.free a).blocks[a']? = M.blocks[a']? := by
  simp [free, List.getElem?_modify_ne _ _ h]

/-- After a free, every access to the freed allocation is UB. -/
theorem locate_free {M : Memory u} {a : AllocId} (ha : a < M.blocks.length) (off : Int)
    (n : Nat) : (M.free a).locate ⟨some a, off⟩ n = .error .freed := by
  have hb : (M.free a).blocks[a]? = some { M.blocks[a] with live := false } := by
    simp [free, ha]
  exact locate_freed hb rfl off n

end Memory

end Fir.Memory
