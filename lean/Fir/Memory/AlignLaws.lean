import Fir.Memory.Laws

/-!
# Aligned access laws

An op's load or store carries an alignment, and is immediate UB when it is
misaligned (the human's ruling of 2026-11-11 on #231). The laws below say
what an aligned access is, from the plain accesses of the previous section:

* Whether an access is aligned depends only on the alignment of its block
  and on its pointer, so it depends on no unit, and a store, which keeps
  every block's shape, changes it for no access.
* An aligned access faults as the plain one does. When the plain one
  succeeds, the aligned one gives what it gives if the access is aligned,
  and is misaligned otherwise.
* Every access is aligned to 1, so an access aligned to 1 is the plain
  access.
* An access at the start of a new allocation is aligned exactly when its
  alignment divides the allocation's.
-/

namespace Fir.Memory

variable {u : Nat}

namespace Memory

/-- Every access is aligned to 1. -/
theorem aligned_one (M : Memory u) (p : Pointer) : M.aligned p 1 = true := by
  unfold aligned
  split
  · rfl
  · split <;> simp

/-- An aligned load faults as the plain load does, and gives what it gives
when the access is aligned. -/
theorem loadAligned_of_aligned {M : Memory u} {p : Pointer} {al : Nat} (h : M.aligned p al = true)
    (n : Nat) : M.loadAligned p n al = M.load p n := by
  unfold loadAligned
  split <;> simp_all

/-- An aligned store faults as the plain store does, and gives what it
gives when the access is aligned. -/
theorem storeAligned_of_aligned {M : Memory u} {p : Pointer} {al : Nat}
    (h : M.aligned p al = true) (us : List (MemUnit u)) :
    M.storeAligned p us al = M.store p us := by
  unfold storeAligned
  split <;> simp_all

/-- A load aligned to 1 is the plain load. -/
theorem loadAligned_one (M : Memory u) (p : Pointer) (n : Nat) :
    M.loadAligned p n 1 = M.load p n :=
  loadAligned_of_aligned (aligned_one M p) n

/-- A store aligned to 1 is the plain store. -/
theorem storeAligned_one (M : Memory u) (p : Pointer) (us : List (MemUnit u)) :
    M.storeAligned p us 1 = M.store p us :=
  storeAligned_of_aligned (aligned_one M p) us

/-- An aligned load gives units exactly when the plain load gives them and
the access is aligned. -/
theorem loadAligned_eq_ok {M : Memory u} {p : Pointer} {n al : Nat} {us : List (MemUnit u)} :
    M.loadAligned p n al = .ok us ↔ M.load p n = .ok us ∧ M.aligned p al = true := by
  unfold loadAligned
  split <;> rename_i h <;> rw [h] <;> by_cases ha : M.aligned p al <;> simp [ha]

/-- An aligned store gives memory exactly when the plain store gives it and
the access is aligned. -/
theorem storeAligned_eq_ok {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)} {al : Nat} :
    M.storeAligned p us al = .ok M' ↔ M.store p us = .ok M' ∧ M.aligned p al = true := by
  unfold storeAligned
  split <;> rename_i h <;> rw [h] <;> by_cases ha : M.aligned p al <;> simp [ha]

/-- An aligned load faults where the plain load faults, for the same
reason. -/
theorem loadAligned_of_error {M : Memory u} {p : Pointer} {n : Nat} {f : Fault}
    (h : M.load p n = .error f) (al : Nat) : M.loadAligned p n al = .error f := by
  simp [loadAligned, h]

/-- An aligned store faults where the plain store faults, for the same
reason. -/
theorem storeAligned_of_error {M : Memory u} {p : Pointer} {us : List (MemUnit u)} {f : Fault}
    (h : M.store p us = .error f) (al : Nat) : M.storeAligned p us al = .error f := by
  simp [storeAligned, h]

/-- A load that the plain load lets through, but that is not aligned, is
misaligned. -/
theorem loadAligned_misaligned {M : Memory u} {p : Pointer} {n al : Nat} {us : List (MemUnit u)}
    (hl : M.load p n = .ok us) (h : M.aligned p al = false) :
    M.loadAligned p n al = .error .misaligned := by
  simp [loadAligned, hl, h]

/-- A store that the plain store lets through, but that is not aligned, is
misaligned. -/
theorem storeAligned_misaligned {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    {al : Nat} (hs : M.store p us = .ok M') (h : M.aligned p al = false) :
    M.storeAligned p us al = .error .misaligned := by
  simp [storeAligned, hs, h]

/-- Whether an access is aligned depends only on the shapes of the
memory's blocks: two memories whose blocks have the same kind, alignment,
size and liveness, one by one, agree on it. -/
theorem aligned_of_shapes {M M' : Memory u} (h : M.blocks.map Block.shape = M'.blocks.map Block.shape)
    (p : Pointer) (al : Nat) : M.aligned p al = M'.aligned p al := by
  obtain ⟨prov, off⟩ := p
  cases prov with
  | none => rfl
  | some a =>
    have k := congrArg (·[a]?) h
    simp only [List.getElem?_map] at k
    unfold aligned
    cases hb : M.blocks[a]? <;> cases hb' : M'.blocks[a]? <;> simp_all [Block.shape]

/-- A store changes for no access whether it is aligned: it keeps every
block's alignment. -/
theorem aligned_store {M M' : Memory u} {p : Pointer} {us : List (MemUnit u)}
    (h : M.store p us = .ok M') (q : Pointer) (al : Nat) : M'.aligned q al = M.aligned q al := by
  obtain ⟨prov, off⟩ := q
  cases prov with
  | none => rfl
  | some a =>
    have k := store_shape h a
    unfold aligned
    cases hb : M'.blocks[a]? <;> cases hb' : M.blocks[a]? <;> simp_all [Block.shape]

/-- An access at the start of a new allocation, aligned to `al`, is
aligned exactly when `al` divides the allocation's alignment. -/
theorem aligned_alloc (M : Memory u) (k : AllocKind) (n al' al : Nat) :
    (M.alloc k n al').2.aligned (M.alloc k n al').1 al = decide (al ∣ al') := by
  simp [aligned, alloc_fst, alloc_blocks_new]

end Memory

end Fir.Memory
