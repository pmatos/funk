import Fir.Memory.AddressLaws

/-!
# Canonical layout laws

The canonical layout lays the allocations of a memory out in the order they
were made (#232). The laws below say what that order gives:

* Every canonical address is at least where its layout starts, and an
  allocation's canonical address is a multiple of its alignment when that
  is not 0.
* An allocation ends, plus the one address it leaves unused, before the
  canonical address of each allocation made after it. So no two canonical
  addresses overlap.
* So while every allocation with an address has its canonical one, the
  canonical address of an allocation fits when it ends below `2 ^ P`, and
  the canonical layout gives it that address.
* Allocating moves no canonical address: an allocation's canonical address
  depends only on the allocations made before it.

The canonical layout never gives an address twice, but the spec does not
promise that. The last law is a witness: a memory in which an allocation
was given the address 4 and freed, and the address 4 fits a later
allocation, so that the later one may be given the same address (the
human's ruling of 2026-11-10 on #232). No law may assume fresh addresses,
since native stack slots are reused.
-/

namespace Fir.Memory

variable {u : Nat}

/-- The layout of `bs` from `c` puts every block at `c` or above it. -/
theorem le_bumpFrom : ∀ (c : Nat) (bs : List (Block u)) (j : Nat), c ≤ bumpFrom c bs j
  | c, [], _ => by simp [bumpFrom]
  | c, b :: _, 0 => le_alignUp c b.align
  | c, b :: bs, j + 1 => by
    have h₁ := le_alignUp c b.align
    have h₂ := le_bumpFrom (alignUp c b.align + b.units.length + 1) bs j
    simp only [bumpFrom]
    omega

/-- A block's canonical address is a multiple of its alignment, when that
is not 0. -/
theorem dvd_bumpFrom : ∀ {c : Nat} {bs : List (Block u)} {a : Nat} {b : Block u},
    bs[a]? = some b → 0 < b.align → b.align ∣ bumpFrom c bs a
  | c, b' :: _, 0, b, h, hal => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact dvd_alignUp c hal
  | _, _ :: bs, a + 1, _, h, hal => by
    simp only [bumpFrom]
    exact dvd_bumpFrom (bs := bs) (a := a) (by simpa using h) hal

/-- A block ends, with the address after it, before the canonical address
of every block after it. -/
theorem bumpFrom_lt : ∀ {c : Nat} {bs : List (Block u)} {i j : Nat} {b : Block u},
    bs[i]? = some b → i < j → bumpFrom c bs i + b.units.length < bumpFrom c bs j
  | c, b' :: bs, 0, j + 1, b, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have := le_bumpFrom (alignUp c b'.align + b'.units.length + 1) bs j
    simp only [bumpFrom]
    omega
  | _, _ :: bs, i + 1, j + 1, _, h, hij => by
    simp only [bumpFrom]
    exact bumpFrom_lt (bs := bs) (i := i) (by simpa using h) (by omega)

/-- A block added after the others moves no canonical address. -/
theorem bumpFrom_append : ∀ {c : Nat} {bs : List (Block u)} {a : Nat} (b : Block u),
    a < bs.length → bumpFrom c (bs ++ [b]) a = bumpFrom c bs a
  | _, _ :: _, 0, _, _ => rfl
  | _, _ :: bs, a + 1, b, h => by
    simp only [List.cons_append, bumpFrom]
    exact bumpFrom_append (bs := bs) b (by simp at h; omega)

namespace Memory

/-- Allocating moves no canonical address. -/
theorem bump_alloc (M : Memory u) (k : AllocKind) (n al : Nat) {a : AllocId}
    (h : a < M.blocks.length) : (M.alloc k n al).2.bump a = M.bump a :=
  bumpFrom_append _ h

/-- The canonical addresses of two allocations do not overlap: the earlier
ends before the later starts. -/
theorem bump_lt {M : Memory u} {i j : AllocId} {b : Block u} (h : M.blocks[i]? = some b)
    (hij : i < j) : M.bump i + b.units.length < M.bump j :=
  bumpFrom_lt h hij

/-- While every allocation with an address has its canonical one, the
canonical address of an allocation aligned to more than 0 fits when it
ends below `2 ^ P`. -/
theorem fits_bump {M : Memory u} {P a : Nat} {b : Block u} (hb : M.blocks[a]? = some b)
    (hal : 0 < b.align) (hcanon : ∀ j z, M.addrOf j = some z → z = M.bump j)
    (hP : M.bump a + b.units.length < 2 ^ P) : M.fits P a (M.bump a) = true := by
  refine fits_eq_true.mpr ⟨b, hb, ?_, dvd_bumpFrom hb hal, hP, ?_⟩
  · have := le_bumpFrom 1 M.blocks a
    exact this
  · intro j c hc hne
    unfold Block.leavesRoom
    cases hz : c.addr with
    | none => rfl
    | some z =>
      have hzj : z = M.bump j := hcanon j z (by simp [addrOf, hc, hz])
      subst hzj
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact .inr (Nat.le_of_lt (bump_lt hc hlt))
      · exact .inl (.inr (Nat.le_of_lt (bump_lt hb hgt)))

/-- So the canonical layout then gives the canonical address. -/
theorem canonical_bump {M : Memory u} {P a : Nat} (h : M.fits P a (M.bump a) = true) :
    M.canonical P a = some (M.bump a) := by
  simp [canonical, h]

end Memory

/-! # Addresses are not fresh -/

/-- The memory of the witness: an allocation of 4 bytes, aligned to 4,
given the address 4 and freed, then a second allocation like it. -/
def reuseWitness : Memory 8 :=
  ((((Memory.empty.alloc .stack 4 4).2.expose 0 4).free 0).alloc .stack 4 4).2

/-- In the witness, the first allocation has the address 4 and is freed,
the address 4 fits the second, with 64-bit pointers, and the second may be
given it. -/
theorem reuseWitness_reuses : reuseWitness.addrOf 0 = some 4 ∧
    reuseWitness.blocks[0]?.map (·.live) = some false ∧ reuseWitness.fits 64 1 4 = true ∧
    (reuseWitness.expose 1 4).addrOf 1 = some 4 := by
  decide

/-- The spec does not imply that a freed allocation's address is never
given to a later allocation. -/
theorem addresses_not_fresh : ¬ ∀ (M : Memory 8) (P a a' x : Nat), a < a' →
    M.addrOf a = some x → M.blocks[a]?.map (·.live) = some false → M.fits P a' x = false := by
  intro h
  have ⟨h₁, h₂, h₃, _⟩ := reuseWitness_reuses
  have := h reuseWitness 64 0 1 4 (by decide) h₁ h₂
  rw [h₃] at this
  exact Bool.noConfusion this

end Fir.Memory
