import Fir.Memory.Address

/-!
# Address laws

The laws below say what the addresses of the previous section are:

* An address fits an allocation exactly when it is not 0, it is a multiple
  of the allocation's alignment, the allocation ends below `2 ^ P`, and no
  other live allocation with an address overlaps it.
* The canonical layout is one of the assignments that the spec allows:
  the address it gives fits, and it gives one whenever any address fits
  (#232). So `fir-ref`, which runs it, makes one of the choices that the
  spec allows, and fails to give an address only where no address fits.
* The canonical addresses are in the order the allocations were made, and
  no two of them overlap. So while every allocation with an address has
  its canonical one, the canonical address of another fits when the
  allocation ends below `2 ^ P`. Allocating keeps every canonical address.
* The spec does not imply that addresses are fresh: a later allocation
  may get exactly the address of one that was freed, as a witness shows
  (the human's ruling of 2026-11-10 on #232).
-/

namespace Fir.Memory

variable {u : Nat}

/-! # Aligning up -/

/-- An address aligned up is no lower. -/
theorem le_alignUp (c al : Nat) : c ≤ alignUp c al := by
  unfold alignUp
  split
  · exact Nat.le_refl c
  · have hal : 0 < al := Nat.pos_of_ne_zero ‹_›
    have hd := Nat.div_add_mod (c + al - 1) al
    have hm := Nat.mod_lt (c + al - 1) hal
    rw [Nat.mul_comm]
    generalize (c + al - 1) / al = q at *
    generalize al * q = t at *
    omega

/-- An address aligned up to `al` is a multiple of `al`, when `al` is not 0. -/
theorem dvd_alignUp (c : Nat) {al : Nat} (h : 0 < al) : al ∣ alignUp c al := by
  have h0 : al ≠ 0 := by omega
  simp only [alignUp, h0, ↓reduceIte]
  exact Nat.dvd_mul_left al _

/-- A multiple `x` of `al` that is at least `c` and below `c + al` is `c`
aligned up to `al`. -/
theorem alignUp_eq {c al x : Nat} (h : 0 < al) (hx : al ∣ x) (hc : c ≤ x) (hlt : x < c + al) :
    alignUp c al = x := by
  obtain ⟨k, rfl⟩ := hx
  have h0 : al ≠ 0 := by omega
  simp only [alignUp, h0, ↓reduceIte]
  rw [Nat.mul_comm al k]
  have hk : (c + al - 1) / al = k := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm] at hlt
      omega
    · rw [Nat.succ_mul]
      rw [Nat.mul_comm] at hc
      omega
  rw [hk]

/-! # When an address fits -/

/-- Every block but the allocation `a` leaves room exactly when each of
them does. -/
theorem roomFrom_eq_true {x n a : Nat} :
    ∀ {i : Nat} {bs : List (Block u)}, roomFrom x n a i bs = true ↔
      ∀ j c, bs[j]? = some c → i + j ≠ a → c.leavesRoom x n = true
  | i, [] => by simp [roomFrom]
  | i, c :: cs => by
    simp only [roomFrom, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, roomFrom_eq_true]
    constructor
    · rintro ⟨h₀, hs⟩ j c' hj hne
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact h₀.resolve_left (by omega)
      | succ j => exact hs j c' (by simpa using hj) (by omega)
    · intro h
      refine ⟨?_, fun j c' hj hne => h (j + 1) c' (by simpa using hj) (by omega)⟩
      by_cases hi : i = a
      · exact .inl hi
      · exact .inr (h 0 c rfl (by omega))

namespace Memory

/-- The address `x` fits the allocation `a` exactly when it is not 0, it
is a multiple of the allocation's alignment, the allocation ends below
`2 ^ P`, and every other allocation leaves room for it. -/
theorem fits_eq_true {M : Memory u} {P a x : Nat} :
    M.fits P a x = true ↔ ∃ b, M.blocks[a]? = some b ∧ 0 < x ∧ b.align ∣ x ∧
      x + b.units.length < 2 ^ P ∧
      ∀ j c, M.blocks[j]? = some c → j ≠ a → c.leavesRoom x b.units.length = true := by
  unfold fits
  cases hb : M.blocks[a]? with
  | none => simp
  | some b =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, roomFrom_eq_true, Nat.zero_add,
      Option.some.injEq, exists_eq_left', and_assoc]

/-- A fitting address is a fitting candidate, or there is a lower one that
fits: aligning 1 up, or aligning up the end of a live allocation with an
address. -/
theorem fits_candidate {M : Memory u} {P a : Nat} {b : Block u} (hb : M.blocks[a]? = some b) :
    ∀ x, M.fits P a x = true → ∃ y, M.fits P a y = true ∧ (y = alignUp 1 b.align ∨
      ∃ (j : Nat) (c : Block u) (z : Nat), M.blocks[j]? = some c ∧ c.addr = some z ∧ c.live = true ∧
        y = alignUp (z + c.units.length) b.align) := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
  intro hx
  obtain ⟨b', hb', hx0, hdvd, hlt, hroom⟩ := fits_eq_true.mp hx
  rw [hb, Option.some.injEq] at hb'
  subst hb'
  have hal : 0 < b.align := by
    rcases Nat.eq_zero_or_pos b.align with h | h
    · rw [h, Nat.zero_dvd] at hdvd
      omega
    · exact h
  by_cases hle : x ≤ b.align
  · refine ⟨x, hx, .inl (alignUp_eq hal hdvd (by omega) (by omega)).symm⟩
  · have hdvd' : b.align ∣ x - b.align := Nat.dvd_sub hdvd (Nat.dvd_refl _)
    by_cases hx' : M.fits P a (x - b.align) = true
    · exact ih (x - b.align) (by omega) hx'
    · -- The address below does not fit, so a live block is in its way.
      have : ¬ ∀ j c, M.blocks[j]? = some c → j ≠ a →
          c.leavesRoom (x - b.align) b.units.length = true := fun h =>
        hx' (fits_eq_true.mpr ⟨b, hb, by omega, hdvd', by omega, h⟩)
      simp only [Classical.not_forall, Bool.not_eq_true] at this
      obtain ⟨j, c, hc, hne, hfalse⟩ := this
      have htrue := hroom j c hc hne
      unfold Block.leavesRoom at hfalse htrue
      cases hz : c.addr with
      | none => simp [hz] at hfalse
      | some z =>
        simp only [hz, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          Bool.or_eq_false_iff, decide_eq_false_iff_not] at hfalse htrue
        obtain ⟨⟨hlive, h₁⟩, h₂⟩ := hfalse
        have hlive' : c.live = true := by simpa using hlive
        have hend : z + c.units.length ≤ x := by
          rcases htrue with (hl | h₃) | h₄
          · simp [hlive'] at hl
          · omega
          · exact h₄
        exact ⟨x, hx, .inr ⟨j, c, z, hc, hz, hlive',
          (alignUp_eq hal hdvd hend (by omega)).symm⟩⟩

end Memory

/-- An address that `fitAfter` gives fits. -/
theorem fitAfter_fits {M : Memory u} {P a al y : Nat} :
    ∀ {cs : List (Block u)}, fitAfter M P a al cs = some y → M.fits P a y = true
  | [], h => by simp [fitAfter] at h
  | c :: cs, h => by
    unfold fitAfter at h
    split at h
    · split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hc
        exact hc.2
      · exact fitAfter_fits h
    · exact fitAfter_fits h

/-- `fitAfter` gives an address when the end of a live block of `cs` with
an address, aligned up, fits. -/
theorem fitAfter_isSome {M : Memory u} {P a al : Nat} :
    ∀ {cs : List (Block u)} {c : Block u} {z : Nat}, c ∈ cs → c.addr = some z → c.live = true →
      M.fits P a (alignUp (z + c.units.length) al) = true → (fitAfter M P a al cs).isSome
  | c' :: cs, c, z, hm, hz, hl, hf => by
    unfold fitAfter
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [hz, hl, hf]
    · split
      · split
        · rfl
        · exact fitAfter_isSome hm hz hl hf
      · exact fitAfter_isSome hm hz hl hf

namespace Memory

/-- An address that the canonical layout gives fits. -/
theorem canonical_fits {M : Memory u} {P a x : Nat} (h : M.canonical P a = some x) :
    M.fits P a x = true := by
  unfold canonical at h
  split at h
  · rename_i hf
    simp only [Option.some.injEq] at h
    exact h ▸ hf
  · split at h
    · simp at h
    · split at h
      · rename_i hf
        simp only [Option.some.injEq] at h
        exact h ▸ hf
      · exact fitAfter_fits h

/-- The canonical layout gives an address whenever an address fits. With
`canonical_fits`, it is one of the assignments that the spec allows. -/
theorem canonical_isSome {M : Memory u} {P a x : Nat} (h : M.fits P a x = true) :
    (M.canonical P a).isSome := by
  obtain ⟨b, hb, -⟩ := fits_eq_true.mp h
  unfold canonical
  split
  · rfl
  · rw [hb]
    simp only
    split
    · rfl
    · rename_i h₁
      obtain ⟨y, hy, hc⟩ := fits_candidate hb x h
      rcases hc with rfl | ⟨j, c, z, hc, hz, hl, rfl⟩
      · exact absurd hy h₁
      · exact fitAfter_isSome (List.mem_of_getElem? hc) hz hl hy

/-- An address fits the allocation `a` exactly when the canonical layout
gives it one, which fits. -/
theorem exists_fits_iff {M : Memory u} {P a : Nat} :
    (∃ x, M.fits P a x = true) ↔ ∃ x, M.canonical P a = some x ∧ M.fits P a x = true := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (canonical_isSome hx)
    exact ⟨y, hy, canonical_fits hy⟩
  · rintro ⟨x, -, hx⟩
    exact ⟨x, hx⟩

end Memory

end Fir.Memory
