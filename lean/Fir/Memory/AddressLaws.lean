import Fir.Memory.Address

/-!
# Address laws

The laws below say what the addresses of the previous section are:

* An address fits an allocation exactly when the allocation stays within
  the bounds, the address is a multiple of its alignment, and no other
  live allocation with an address overlaps it.
* The lowest address that fits is a candidate: the first multiple of the
  alignment from the lower bound, or the first from where a live
  allocation with an address ends.
* The canonical layout is one of the assignments that the spec allows:
  the address it gives fits, and it gives one whenever any address fits
  (#232). When the canonical address does not fit, it gives the lowest
  address that fits. So `fir-ref`, which runs it, makes one of the choices
  that the spec allows, and fails to give an address only where no address
  fits.
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

/-- The address `x` fits the allocation `a` exactly when the allocation
stays from `lo` to `hi`, `x` is a multiple of its alignment, and every
other allocation leaves room for it. -/
theorem fits_eq_true {M : Memory u} {lo hi a x : Nat} :
    M.fits lo hi a x = true ↔ ∃ b, M.blocks[a]? = some b ∧ lo ≤ x ∧ b.align ∣ x ∧
      x + b.units.length ≤ hi ∧
      ∀ j c, M.blocks[j]? = some c → j ≠ a → c.leavesRoom x b.units.length = true := by
  unfold fits
  cases hb : M.blocks[a]? with
  | none => simp
  | some b =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, roomFrom_eq_true, Nat.zero_add,
      Option.some.injEq, exists_eq_left', and_assoc]

/-- A fitting address is a candidate, or a lower address fits: the
candidates are the first multiple of the alignment from `lo`, and the first
multiples from where each live allocation with an address ends. -/
theorem fits_candidate {M : Memory u} {lo hi a : Nat} {b : Block u} (hb : M.blocks[a]? = some b)
    {x : Nat} (hx : M.fits lo hi a x = true) : (x = alignUp lo b.align ∨
      ∃ (j : Nat) (c : Block u) (z : Nat), M.blocks[j]? = some c ∧ c.addr = some z ∧
        c.live = true ∧ x = alignUp (z + c.units.length) b.align) ∨
      ∃ y, y < x ∧ M.fits lo hi a y = true := by
  obtain ⟨b', hb', hlo, hdvd, hhi, hroom⟩ := fits_eq_true.mp hx
  rw [hb, Option.some.injEq] at hb'
  subst hb'
  rcases Nat.eq_zero_or_pos b.align with h0 | hal
  · -- Aligned to 0, the allocation fits only at 0, which is `lo` aligned up.
    rw [h0, Nat.zero_dvd] at hdvd
    subst hdvd
    refine .inl (.inl ?_)
    simp only [alignUp, h0, ↓reduceIte]
    omega
  by_cases hle : x < lo + b.align
  · exact .inl (.inl (alignUp_eq hal hdvd hlo hle).symm)
  · have hdvd' : b.align ∣ x - b.align := Nat.dvd_sub hdvd (Nat.dvd_refl _)
    by_cases hx' : M.fits lo hi a (x - b.align) = true
    · exact .inr ⟨x - b.align, by omega, hx'⟩
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
        exact .inl (.inr ⟨j, c, z, hc, hz, hlive',
          (alignUp_eq hal hdvd hend (by omega)).symm⟩)

end Memory

/-! # The lowest address that fits -/

/-- Keeping the lower of an address found so far and another gives one at
most each of them. -/
theorem keepLow_le {best : Option Nat} {z : Nat} :
    ∃ y, keepLow best z = some y ∧ y ≤ z ∧ ∀ b, best = some b → y ≤ b := by
  cases best with
  | none => exact ⟨z, rfl, Nat.le_refl z, fun _ h => nomatch h⟩
  | some b =>
    exact ⟨min b z, rfl, Nat.min_le_right b z, fun _ h => by
      cases h; exact Nat.min_le_left _ _⟩

/-- The lowest address of `lowestFrom` fits, when the one it starts with
does. -/
theorem lowestFrom_fits {M : Memory u} {lo hi a al y : Nat} :
    ∀ {best : Option Nat} {cs : List (Block u)}, (∀ b, best = some b → M.fits lo hi a b = true) →
      lowestFrom M lo hi a al best cs = some y → M.fits lo hi a y = true
  | best, [], hb, h => hb y h
  | best, c :: cs, hb, h => by
    unfold lowestFrom at h
    refine lowestFrom_fits ?_ h
    intro b' hb'
    split at hb'
    · split at hb'
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        cases best with
        | none =>
          simp only [keepLow, Option.some.injEq] at hb'
          exact hb' ▸ hc.2
        | some b₀ =>
          simp only [keepLow, Option.some.injEq] at hb'
          rw [← hb']
          rcases Nat.le_total b₀ (alignUp (_ + c.units.length) al) with hle | hle
          · rw [Nat.min_eq_left hle]
            exact hb b₀ rfl
          · rw [Nat.min_eq_right hle]
            exact hc.2
      · exact hb b' hb'
    · exact hb b' hb'

/-- `lowestFrom` gives an address at most the one it starts with. -/
theorem lowestFrom_le_best {M : Memory u} {lo hi a al : Nat} :
    ∀ {best : Option Nat} {cs : List (Block u)} {b : Nat}, best = some b →
      ∃ y, lowestFrom M lo hi a al best cs = some y ∧ y ≤ b
  | _, [], b, h => ⟨b, h, Nat.le_refl b⟩
  | best, c :: cs, b, h => by
    unfold lowestFrom
    split
    · split
      · obtain ⟨y, hy, -, hyb⟩ := keepLow_le (best := best) (z := alignUp (_ + c.units.length) al)
        obtain ⟨y', hy', hle⟩ := lowestFrom_le_best (M := M) (lo := lo) (hi := hi) (a := a)
          (al := al) (cs := cs) hy
        exact ⟨y', hy', Nat.le_trans hle (hyb b h)⟩
      · exact lowestFrom_le_best h
    · exact lowestFrom_le_best h

/-- `lowestFrom` gives an address at most the end of each live block of
`cs` with an address, aligned up, that fits. -/
theorem lowestFrom_le_after {M : Memory u} {lo hi a al : Nat} :
    ∀ {best : Option Nat} {cs : List (Block u)} {c : Block u} {z : Nat}, c ∈ cs →
      c.addr = some z → c.live = true → M.fits lo hi a (alignUp (z + c.units.length) al) = true →
      ∃ y, lowestFrom M lo hi a al best cs = some y ∧ y ≤ alignUp (z + c.units.length) al
  | best, c' :: cs, c, z, hm, hz, hl, hf => by
    rcases List.mem_cons.mp hm with rfl | hm
    · unfold lowestFrom
      simp only [hz, hl, hf, Bool.and_self, ↓reduceIte]
      obtain ⟨y, hy, hyz, -⟩ := keepLow_le (best := best) (z := alignUp (z + c.units.length) al)
      obtain ⟨y', hy', hle⟩ := lowestFrom_le_best (M := M) (lo := lo) (hi := hi) (a := a)
        (al := al) (cs := cs) hy
      exact ⟨y', hy', Nat.le_trans hle hyz⟩
    · unfold lowestFrom
      exact lowestFrom_le_after hm hz hl hf

namespace Memory

/-- The lowest fit fits. -/
theorem lowestFit_fits {M : Memory u} {lo hi a x : Nat} (h : M.lowestFit lo hi a = some x) :
    M.fits lo hi a x = true := by
  unfold lowestFit at h
  split at h
  · simp at h
  · refine lowestFrom_fits ?_ h
    intro b hb
    split at hb
    · rename_i hf
      simp only [Option.some.injEq] at hb
      exact hb ▸ hf
    · simp at hb

/-- The lowest fit is at most every address that fits. -/
theorem lowestFit_le {M : Memory u} {lo hi a : Nat} :
    ∀ x, M.fits lo hi a x = true → ∃ y, M.lowestFit lo hi a = some y ∧ y ≤ x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
  intro hx
  obtain ⟨b, hb, -⟩ := fits_eq_true.mp hx
  rcases fits_candidate hb hx with (rfl | ⟨j, c, z, hc, hz, hl, rfl⟩) | ⟨y, hyx, hy⟩
  · unfold lowestFit
    rw [hb]
    simp only [hx, ↓reduceIte]
    exact lowestFrom_le_best rfl
  · unfold lowestFit
    rw [hb]
    exact lowestFrom_le_after (List.mem_of_getElem? hc) hz hl hx
  · obtain ⟨y', hy', hle⟩ := ih y hyx hy
    exact ⟨y', hy', Nat.le_trans hle (Nat.le_of_lt hyx)⟩

/-- An address that the canonical layout gives fits. -/
theorem canonical_fits {M : Memory u} {lo hi a x : Nat} (h : M.canonical lo hi a = some x) :
    M.fits lo hi a x = true := by
  unfold canonical at h
  dsimp only at h
  split at h
  · rename_i hf
    simp only [Option.some.injEq] at h
    exact h ▸ hf
  · exact lowestFit_fits h

/-- When the canonical address does not fit, the canonical layout gives an
address at most every address that fits: the lowest. -/
theorem canonical_lowest {M : Memory u} {lo hi a x : Nat}
    (hb : M.fits lo hi a (M.bump lo a) = false) (h : M.fits lo hi a x = true) :
    ∃ y, M.canonical lo hi a = some y ∧ y ≤ x := by
  unfold canonical
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  exact lowestFit_le x h

/-- The canonical layout gives an address whenever an address fits. With
`canonical_fits`, it is one of the assignments that the spec allows. -/
theorem canonical_isSome {M : Memory u} {lo hi a x : Nat} (h : M.fits lo hi a x = true) :
    (M.canonical lo hi a).isSome := by
  cases hb : M.fits lo hi a (M.bump lo a) with
  | true => simp [canonical, hb]
  | false =>
    obtain ⟨y, hy, -⟩ := canonical_lowest hb h
    simp [hy]

/-- An address fits the allocation `a` exactly when the canonical layout
gives it one, which fits. -/
theorem exists_fits_iff {M : Memory u} {lo hi a : Nat} :
    (∃ x, M.fits lo hi a x = true) ↔
      ∃ x, M.canonical lo hi a = some x ∧ M.fits lo hi a x = true := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (canonical_isSome hx)
    exact ⟨y, hy, canonical_fits hy⟩
  · rintro ⟨x, -, hx⟩
    exact ⟨x, hx⟩

end Memory

end Fir.Memory
