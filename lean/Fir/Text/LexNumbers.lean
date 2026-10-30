import Fir.Text.Tokens

/-!
# Reading printed numbers

The printer writes a natural number with `Nat.toDigits 10`, through
`toString`, and the code point of an escaped character with
`Nat.toDigits 16`, through `hex`. The lexer reads the digits back with
`digitsValue` and `hexValue`. This section proves that each reads back the
number that was written, and that the digits have the shape the lexer
expects: decimal or lowercase hexadecimal digits, with no leading zero.

`digitsValue` reads a long number in two halves, joined by one product.
That changes only how long it takes: it gives the value of a left-to-right
reading, `Nat.ofDigitChars 10`, for every list of digits
(`digitsValue_eq_ofDigitChars`).
-/

namespace Fir.Text

/-- `digitsValue` gives the value of a left-to-right reading of the digits,
at every length. -/
theorem digitsValue_eq_ofDigitChars (ds : List Char) : digitsValue ds = Nat.ofDigitChars 10 ds 0 := by
  induction ds using digitsValue.induct with
  | case1 ds h => rw [digitsValue]; simp only [h, ite_true]; rfl
  | case2 ds h k ih₁ ih₂ =>
    rw [digitsValue]
    simp only [h, ite_false]
    dsimp only [k] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
    have hl : (List.drop (ds.length - ds.length / 2) ds).length = ds.length / 2 := by
      rw [List.length_drop]; omega
    conv => rhs; rw [← List.take_append_drop (ds.length - ds.length / 2) ds]
    rw [Nat.ofDigitChars_append, Nat.ofDigitChars_eq_ofDigitChars_zero (l := List.drop _ ds)
      (init := Nat.ofDigitChars 10 (List.take _ ds) 0), hl, Nat.mul_comm]

/-- The digits that `toString` writes for a natural number read back as it. -/
theorem digitsValue_toDigits (n : Nat) : digitsValue (Nat.toDigits 10 n) = n := by
  rw [digitsValue_eq_ofDigitChars, Nat.ofDigitChars_ten_toDigits]

/-- The value of one hexadecimal digit, as `hexValue` reads it. -/
def hexDigitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

theorem hexValue_append (l : List Char) (c : Char) :
    hexValue (l ++ [c]) = 16 * hexValue l + hexDigitValue c := by
  simp [hexValue, hexDigitValue, List.foldl_append]

/-- Each digit below 16 is a lowercase hexadecimal digit, read back as itself. -/
theorem digitChar_hex : ∀ k, k < 16 →
    isHexDigit (Nat.digitChar k) = true ∧ hexDigitValue (Nat.digitChar k) = k := by
  decide

/-- Each digit below 16 is `0` only for zero. -/
theorem digitChar_ne_zero : ∀ k, k < 16 → 0 < k → Nat.digitChar k ≠ '0' := by
  decide

/-- The digits that `hex` writes for a natural number read back as it. -/
theorem hexValue_toDigits (n : Nat) : hexValue (Nat.toDigits 16 n) = n := by
  induction n using Nat.base_induction 16 (by decide) with
  | single m hm =>
    rw [Nat.toDigits_of_lt_base hm, ← List.nil_append [_], hexValue_append, (digitChar_hex m hm).2]
    simp [hexValue]
  | digit m k hk hm ih =>
    rw [← Nat.toDigits_append_toDigits (by decide) hm hk, Nat.toDigits_of_lt_base hk, hexValue_append,
      ih, (digitChar_hex k hk).2]

/-- Every digit of a number in base `b` is a digit below `b`. -/
theorem mem_toDigits {b n : Nat} (hb : 1 < b) {c : Char} (hc : c ∈ Nat.toDigits b n) :
    ∃ k, k < b ∧ c = Nat.digitChar k := by
  induction n using Nat.base_induction b hb with
  | single m hm =>
    rw [Nat.toDigits_of_lt_base hm, List.mem_singleton] at hc
    exact ⟨m, hm, hc⟩
  | digit m k hk hm ih =>
    rw [← Nat.toDigits_append_toDigits hb hm hk, Nat.toDigits_of_lt_base hk, List.mem_append,
      List.mem_singleton] at hc
    rcases hc with hc | hc
    · exact ih hc
    · exact ⟨k, hk, hc⟩

/-- Every digit that `hex` writes is a lowercase hexadecimal digit. -/
theorem isHexDigit_of_mem_toDigits {n : Nat} {c : Char} (hc : c ∈ Nat.toDigits 16 n) :
    isHexDigit c = true := by
  obtain ⟨k, hk, rfl⟩ := mem_toDigits (by decide) hc
  exact (digitChar_hex k hk).1

/-- A number above zero is written without a leading zero, in every base up
to 16. -/
theorem head_toDigits_ne_zero {b n : Nat} (hb : 1 < b) (hb' : b ≤ 16) (hn : 0 < n) :
    (Nat.toDigits b n).head? ≠ some '0' := by
  induction n using Nat.base_induction b hb with
  | single m hm =>
    rw [Nat.toDigits_of_lt_base hm]
    simpa using digitChar_ne_zero m (by omega) hn
  | digit m k hk hm ih =>
    rw [← Nat.toDigits_append_toDigits hb hm hk, List.head?_append]
    obtain ⟨d, ds, he⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (b := b) (n := m))
    have := ih hm
    rw [he] at this ⊢
    simpa using this

end Fir.Text
