import Fir.Core.FloatText
import Fir.Text.LexNumbers

/-!
# Float constants read back

The spelling of a float constant reads back as its bits, and a literal
that reads as bits is their spelling (ADR-2026-11-11-1438). The first
holds by the shape of `floatLit`: it takes a decimal only when the decimal
reads back, and its hexadecimal bits always do. The second holds because
`decodeFloatLit` checks it. Every spelling can be written: a decimal's
fraction and hexadecimal bits are one or more digits of their kind. These
are what the core dialect's text laws ask of a float constant.
-/

namespace Fir.Core

open Text

theorem hexValue_replicate_zero (z : Nat) (ds : List Char) :
    hexValue (List.replicate z '0' ++ ds) = hexValue ds := by
  have h : ∀ k, (List.replicate k '0').foldl
      (fun n c => 16 * n + if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10) 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ', List.foldl_append, ih]; decide
  simp only [hexValue, List.foldl_append, h]

/-- Hexadecimal bits read back as the bits they write. -/
theorem readFloatLit_hexLit (e m : Nat) (b : BitVec (floatWidth e m)) :
    readFloatLit e m (hexLit _ b) = some b := by
  have hw : 0 < (floatWidth e m + 3) / 4 := by simp [floatWidth]; omega
  have hlt : b.toNat < 16 ^ ((floatWidth e m + 3) / 4) := by
    have h₁ := b.isLt
    have h₂ : 2 ^ floatWidth e m ≤ 16 ^ ((floatWidth e m + 3) / 4) := by
      rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hl := (Nat.length_toDigits_le_iff (b := 16) (by decide) hw).mpr hlt
  simp only [hexLit, readFloatLit, padDigits, List.length_append, List.length_replicate,
    hexValue_replicate_zero, hexValue_toDigits, b.isLt, and_true, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  simp only [ite_eq_left_iff]
  omega

/-- The digits that `padDigits` writes of a number in base 10 or 16 are
digits of that base. -/
theorem mem_padDigits {k : Nat} {ds : List Char} {c : Char} (h : c ∈ padDigits k ds) :
    c = '0' ∨ c ∈ ds := by
  simp only [padDigits, List.mem_append, List.mem_replicate] at h
  rcases h with ⟨-, h⟩ | h
  · exact .inl h
  · exact .inr h

theorem padDigits_ne_nil (k : Nat) {ds : List Char} (h : ds ≠ []) : padDigits k ds ≠ [] := by
  simp [padDigits, h]

/-- The decimal digits of a number are digits. -/
theorem isDigit_of_padDigits {k n : Nat} {c : Char} (h : c ∈ padDigits k (Nat.toDigits 10 n)) :
    c.isDigit = true := by
  rcases mem_padDigits h with rfl | h
  · decide
  · exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- A decimal laid out by `decimalLayout` can be written. -/
theorem decimalLayout_valid (neg : Bool) (c : Nat) (j : Int) : (decimalLayout neg c j).valid = true := by
  have hp : ∀ k n, padDigits k (Nat.toDigits 10 n) ≠ [] ∧
      ∀ x ∈ padDigits k (Nat.toDigits 10 n), x.isDigit = true :=
    fun k n => ⟨padDigits_ne_nil k Nat.toDigits_ne_nil, fun _ hx => isDigit_of_padDigits hx⟩
  unfold decimalLayout
  dsimp only
  split
  · split
    · simp [FloatLit.valid]
    · simp only [FloatLit.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true]
      exact hp _ _
  · split
    · simp [FloatLit.valid]
    · simp only [FloatLit.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true]
      exact hp _ _

/-- Hexadecimal bits can be written. -/
theorem hexLit_valid (w : Nat) (b : BitVec w) : (hexLit w b).valid = true := by
  simp only [hexLit, FloatLit.valid, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true]
  refine ⟨padDigits_ne_nil _ Nat.toDigits_ne_nil, fun c hc => ?_⟩
  rcases mem_padDigits hc with rfl | hc
  · decide
  · exact isHexDigit_of_mem_toDigits hc

/-- A decimal that `decimalLit` gives can be written. -/
theorem decimalLit_valid {e m : Nat} {b : BitVec (floatWidth e m)} {l : FloatLit}
    (h : decimalLit e m b = some l) : l.valid = true := by
  unfold decimalLit at h
  split at h
  · dsimp only at h
    split at h
    · cases h; simp [FloatLit.valid]
    · obtain ⟨⟨c, j⟩, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact decimalLayout_valid _ _ _
    · cases h
  · cases h

/-- The spelling of every float can be written. -/
theorem floatLit_valid (e m : Nat) (b : BitVec (floatWidth e m)) : (floatLit e m b).valid = true := by
  unfold floatLit
  split
  · rename_i l hl
    split
    · exact decimalLit_valid hl
    · exact hexLit_valid _ _
  · exact hexLit_valid _ _

/-- The spelling of a float reads back as it. -/
theorem decodeFloatLit_floatLit (e m : Nat) (b : BitVec (floatWidth e m)) :
    decodeFloatLit e m (floatLit e m b) = some b := by
  have key : readFloatLit e m (floatLit e m b) = some b := by
    unfold floatLit
    split
    · split
      · assumption
      · exact readFloatLit_hexLit e m b
    · exact readFloatLit_hexLit e m b
  simp [decodeFloatLit, key]

/-- A literal that reads as a float is its spelling. -/
theorem floatLit_of_decode {e m : Nat} {l : FloatLit} {b : BitVec (floatWidth e m)}
    (h : decodeFloatLit e m l = some b) : floatLit e m b = l := by
  unfold decodeFloatLit at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

end Fir.Core
