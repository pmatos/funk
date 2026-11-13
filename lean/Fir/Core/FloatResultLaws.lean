import Fir.Core.Semantics
import Fir.Execution.Morphism

/-!
# What a float result may be

These facts about the result of a float op hold for every operation of
Lean's model and every flag. In the set monad, a float result has a way to
end, and every way it ends is a value, never UB: the model's bits, a NaN,
a zero of either sign, or poison. It is poison only when a flag that may
make poison, `nnan` or `ninf`, is set; without them, it is defined bits.

A flag only adds results. With fewer flags, each result of the op is a
result with more of them, or the op with more flags may give poison, which
every value refines. The section on the float arithmetic obligations
builds the obligations of each op on these facts, and the section on
dropping fast-math flags the refinement between flagged ops.

Last, a morphism of monads that keeps choice and UB maps each result in one
monad to the result in the other.
-/

namespace Fir.Core

open Float.Model

/-- In the set monad, any NaN gives exactly the NaNs that a choice of
`m + 1` bits gives. -/
theorem anyNaN_iff {e m : Nat} {ev : Ev (PoisonOr (BitVec (floatWidth e m)))} :
    anyNaN (μ := SetM) e m ev ↔ ∃ c, ev = .ok (.value (nanBits e m c)) := by
  constructor
  · rintro (⟨c, -, h⟩ | ⟨_, ⟨_, h⟩, _⟩)
    · exact ⟨c, h⟩
    · cases h
  · rintro ⟨c, rfl⟩
    exact .inl ⟨c, ⟨c, rfl⟩, rfl⟩

/-- In the set monad, `b` with either sign gives exactly `b` with its sign
flipped by a bit. -/
theorem anySign_iff {e m : Nat} {b : BitVec (floatWidth e m)}
    {ev : Ev (PoisonOr (BitVec (floatWidth e m)))} :
    anySign (μ := SetM) e m b ev ↔ ∃ c, ev = .ok (.value (flipSign e m c b)) := by
  constructor
  · rintro (⟨c, -, h⟩ | ⟨_, ⟨_, h⟩, _⟩)
    · exact ⟨c, h⟩
    · cases h
  · rintro ⟨c, rfl⟩
    exact .inl ⟨c, ⟨c, rfl⟩, rfl⟩

/-- Flipping the sign by a clear bit keeps the bits. -/
theorem flipSign_zero (e m : Nat) (b : BitVec (floatWidth e m)) : flipSign e m 0 b = b := by
  simp [flipSign]

/-- Flags that make no poison make no operand break them. -/
theorem operandsBreak_eq_false {fl : FastMath} (h : fl.mayPoison = false) (e m : Nat)
    (as : List (BitVec (floatWidth e m))) : operandsBreak fl e m as = false := by
  simp only [FastMath.mayPoison, Bool.or_eq_false_iff] at h
  unfold operandsBreak FastMath.breaks
  split <;> simp [h.1, h.2]

/-- An operand that breaks fewer flags breaks more of them. -/
theorem operandsBreak_mono {fl fl' : FastMath} (hle : fl'.Le fl) {e m : Nat}
    {as : List (BitVec (floatWidth e m))} (h : operandsBreak fl' e m as = true) :
    operandsBreak fl e m as = true := by
  unfold operandsBreak FastMath.breaks at *
  by_cases hf : 2 ≤ e ∧ 0 < m
  · simp only [hf, and_self, ↓reduceDIte, List.any_eq_true, Bool.or_eq_true,
      Bool.and_eq_true] at h ⊢
    obtain ⟨a, ha, h⟩ := h
    exact ⟨a, ha, h.imp (fun h => ⟨hle.nnan h.1, h.2⟩) (fun h => ⟨hle.ninf h.1, h.2⟩)⟩
  · simp [hf] at h

/-- A computation of one float value that has a way to end, and every way
it ends is a value: it is never UB. -/
structure Ends {α : Type} (s : SetM α) : Prop where
  ok : ∀ ev, s ev → ∃ v, ev = .ok v
  some : ∃ v, s (.ok v)

/-- `pure` has a way to end, and is never UB. -/
theorem pure_ends {α : Type} (a : α) : Ends (pure a : SetM α) where
  ok _ h := ⟨_, h⟩
  some := ⟨a, rfl⟩

/-- A result that is not a NaN, under the flags, ends with a value: poison
only for a broken `ninf`, and otherwise defined bits. -/
theorem flagResult_ok {fl : FastMath} {e m : Nat} {b : BitVec (floatWidth e m)}
    {u : UnpackedFloat} {ev : Ev (PoisonOr (BitVec (floatWidth e m)))}
    (h : flagResult (μ := SetM) fl e m b u ev) :
    ∃ v, ev = .ok v ∧ (fl.mayPoison = false → ∃ x, v = .value x) := by
  unfold flagResult at h
  split at h
  · rename_i hi
    refine ⟨_, h, fun hm => ?_⟩
    simp [FastMath.mayPoison] at hm hi
    simp_all
  · split at h
    · obtain ⟨c, rfl⟩ := anySign_iff.1 h
      exact ⟨_, rfl, fun _ => ⟨_, rfl⟩⟩
    · exact ⟨_, h, fun _ => ⟨_, rfl⟩⟩

/-- A result that is not a NaN, under the flags, has a way to end. -/
theorem flagResult_some (fl : FastMath) (e m : Nat) (b : BitVec (floatWidth e m))
    (u : UnpackedFloat) : ∃ v, flagResult (μ := SetM) fl e m b u (.ok v) := by
  unfold flagResult
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, anySign_iff.2 ⟨0, rfl⟩⟩
    · exact ⟨_, rfl⟩

/-- In the set monad, every way a float result ends is a value, and it is
defined bits when no flag may make poison. -/
theorem floatResult_ok {fl : FastMath} {e m : Nat} {as : List (BitVec (floatWidth e m))}
    {r : Format → (BitVec (floatWidth e m) → UnpackedFloat) → UnpackedFloat}
    {ev : Ev (PoisonOr (BitVec (floatWidth e m)))} (h : floatResult (μ := SetM) fl e m as r ev) :
    ∃ v, ev = .ok v ∧ (fl.mayPoison = false → ∃ x, v = .value x) := by
  unfold floatResult at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hb
      exact ⟨_, h, fun hm => by rw [operandsBreak_eq_false hm] at hb; cases hb⟩
    · split at h
      · split at h
        · rename_i hn
          exact ⟨_, h, fun hm => by simp [FastMath.mayPoison, hn] at hm⟩
        · obtain ⟨c, rfl⟩ := anyNaN_iff.1 h
          exact ⟨_, rfl, fun _ => ⟨_, rfl⟩⟩
      · exact flagResult_ok h
  · obtain ⟨c, rfl⟩ := anyNaN_iff.1 h
    exact ⟨_, rfl, fun _ => ⟨_, rfl⟩⟩

/-- A float result has a way to end, and is never UB. -/
theorem floatResult_ends {fl : FastMath} (e m : Nat) {as : List (BitVec (floatWidth e m))}
    (r : Format → (BitVec (floatWidth e m) → UnpackedFloat) → UnpackedFloat) :
    Ends (floatResult (μ := SetM) fl e m as r) where
  ok ev h := (floatResult_ok h).imp fun _ h => h.1
  some := by
    unfold floatResult
    split
    · dsimp only
      split
      · exact ⟨_, rfl⟩
      · split
        · split
          · exact ⟨_, rfl⟩
          · exact ⟨_, anyNaN_iff.2 ⟨0, rfl⟩⟩
        · exact flagResult_some _ _ _ _ _
    · exact ⟨_, anyNaN_iff.2 ⟨0, rfl⟩⟩

/-- In the set monad, a float result without flags, such as a conversion's,
is a defined value. -/
theorem floatResult_defined (e m : Nat)
    (r : Format → (BitVec (floatWidth e m) → UnpackedFloat) → UnpackedFloat)
    (ev : Ev (PoisonOr (BitVec (floatWidth e m)))) (h : floatResult (μ := SetM) {} e m [] r ev) :
    ∃ b, ev = .ok (.value b) := by
  obtain ⟨_, rfl, hv⟩ := floatResult_ok h
  obtain ⟨b, rfl⟩ := hv rfl
  exact ⟨b, rfl⟩

/-! # A flag only adds results -/

/-- Under fewer flags, a result that is not a NaN gives a value that the
result under more flags gives too, or the latter may give poison. -/
theorem flagResult_drop {fl fl' : FastMath} (hle : fl'.Le fl) {e m : Nat}
    {b : BitVec (floatWidth e m)} {u : UnpackedFloat} {v : PoisonOr (BitVec (floatWidth e m))}
    (h : flagResult (μ := SetM) fl' e m b u (.ok v)) :
    flagResult (μ := SetM) fl e m b u (.ok .poison) ∨ flagResult (μ := SetM) fl e m b u (.ok v) := by
  unfold flagResult at h ⊢
  split
  · exact .inl rfl
  · rename_i hi
    right
    split at h
    · rename_i hi'
      simp only [Bool.and_eq_true] at hi hi'
      exact absurd ⟨hle.ninf hi'.1, hi'.2⟩ hi
    · split at h
      · rename_i hz
        split
        · exact h
        · rename_i hz'
          simp only [Bool.and_eq_true] at hz hz'
          exact absurd ⟨hle.nsz hz.1, hz.2⟩ hz'
      · cases h
        split
        · exact anySign_iff.2 ⟨0, by rw [flipSign_zero]⟩
        · rfl

/-- Under fewer flags, a float result gives a value that the result under
more flags gives too, or the latter may give poison. -/
theorem floatResult_drop {fl fl' : FastMath} (hle : fl'.Le fl) {e m : Nat}
    {as : List (BitVec (floatWidth e m))}
    {r : Format → (BitVec (floatWidth e m) → UnpackedFloat) → UnpackedFloat}
    {v : PoisonOr (BitVec (floatWidth e m))} (h : floatResult (μ := SetM) fl' e m as r (.ok v)) :
    floatResult (μ := SetM) fl e m as r (.ok .poison) ∨
      floatResult (μ := SetM) fl e m as r (.ok v) := by
  unfold floatResult at h ⊢
  split
  · split at h
    · dsimp only at h ⊢
      split
      · exact .inl rfl
      · rename_i hb
        split at h
        · rename_i hb'
          exact absurd (operandsBreak_mono hle hb') hb
        · split
          · split
            · exact .inl rfl
            · rename_i hn hnn
              right
              split at h
              · split at h
                · rename_i hnn'
                  exact absurd (hle.nnan hnn') hnn
                · exact h
              · contradiction
          · split at h
            · contradiction
            · exact flagResult_drop hle h
    · contradiction
  · split at h
    · contradiction
    · exact .inr h

/-! # Results in another monad -/

section
variable {μ ν : Type → Type} [Monad μ] [Monad ν] [MonadChoice μ] [MonadChoice ν] [MonadUB μ]
  [MonadUB ν] (φ : MonadMorphism μ ν) (hk : φ.KeepsChoiceUB) {e m : Nat}
include hk

/-- A morphism that keeps choice and UB maps any NaN in `μ` to any NaN in
`ν`. -/
theorem anyNaN_map : φ.map (anyNaN (μ := μ) e m) = anyNaN e m := by
  unfold anyNaN
  rw [φ.map_bind, hk.choose]
  simp only [φ.map_pure]

/-- Such a morphism maps `b` with either sign in `μ` to the same in `ν`. -/
theorem anySign_map (b : BitVec (floatWidth e m)) :
    φ.map (anySign (μ := μ) e m b) = anySign e m b := by
  unfold anySign
  rw [φ.map_bind, hk.choose]
  simp only [φ.map_pure]

/-- Such a morphism maps a result that is not a NaN, under the flags, in
`μ` to the same in `ν`. -/
theorem flagResult_map (fl : FastMath) (b : BitVec (floatWidth e m)) (u : UnpackedFloat) :
    φ.map (flagResult (μ := μ) fl e m b u) = flagResult fl e m b u := by
  unfold flagResult
  split
  · exact φ.map_pure _
  · split
    · exact anySign_map φ hk b
    · exact φ.map_pure _

/-- Such a morphism maps a float result in `μ` to the float result in
`ν`. -/
theorem floatResult_map {fl : FastMath} {as : List (BitVec (floatWidth e m))}
    (r : Format → (BitVec (floatWidth e m) → UnpackedFloat) → UnpackedFloat) :
    φ.map (floatResult (μ := μ) fl e m as r) = floatResult fl e m as r := by
  unfold floatResult
  split
  · dsimp only
    split
    · exact φ.map_pure _
    · split
      · split
        · exact φ.map_pure _
        · exact anyNaN_map φ hk
      · exact flagResult_map φ hk _ _ _
  · exact anyNaN_map φ hk

end

end Fir.Core
