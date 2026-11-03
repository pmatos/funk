import Fir.Text.Lexical

/-!
`fir-ref` writes integers with `printDecimal`, not with the spec's
`printInt`. `printInt` calls core's `Int.repr`, which writes a number one
decimal digit at a time and divides the whole number by ten for each one,
so it takes time quadratic in the number of digits. A core constant of type
`i16777215` can have over five million digits, and `printInt` takes hours
to write one (#41).

`printDecimal` splits a number in two at a power of ten, writes the high
part, then the low part with its leading zeros, and splits each part again
in the same way, down to parts of 18 digits. Such a part fits in one
machine word, and `printDecimal` lists its digits from the last one. The
powers are `10^18`, its square, the square of that, and so on: each is
computed once, as a square, and a part of `2k` digits is split at `10^k`.
Lean's natural numbers divide and multiply with GMP, whose products of
large numbers take time close to linear in their size. So `printDecimal`
takes about `log2 (n / 18)` rounds for `n` digits, each a few divisions and
products of numbers of `n` digits in all.

Every part of the text is appended to one accumulator, which each function
below takes and returns, so that Lean appends to it in place. The theorem
`printInt_eq_printDecimal` proves `printDecimal` equal to `printInt`, and
`@[csimp]` makes Lean compile every later call of `printInt` as a call of
`printDecimal` (ADR-2026-10-30-1450). `FirRef.PrintAttr` imports this
module: its `printAttrs` writes the integers of attributes, and Lean
compiles it there, where it would otherwise inline `printInt` and call
`Int.repr` (ADR-2026-11-03-1603).
-/

namespace FirRef

open Fir.Text

/-- The `k` lowest decimal digits of `n`, the most significant first, with
leading zeros. -/
def lowDigits : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, n => lowDigits k (n / 10) ++ [Nat.digitChar (n % 10)]

/-- `lowDigits k n`, then `l`. It puts the last digit first, so each call
is a tail call. -/
def digitsOnto : Nat → Nat → List Char → List Char
  | 0, _, l => l
  | k + 1, n, l => digitsOnto k (n / 10) (Nat.digitChar (n % 10) :: l)

/-- A power of ten and its exponent. -/
structure Pow10 where
  /-- The exponent. -/
  exp : Nat
  /-- The power, `10 ^ exp`. -/
  val : Nat
  /-- The power is `10 ^ exp`. -/
  val_eq : val = 10 ^ exp

/-- `10^18`, the largest power of ten below `2^63`, so that Lean holds a
number below it in one machine word. -/
def pow18 : Pow10 := ⟨18, 1000000000000000000, rfl⟩

/-- The square of a power of ten. -/
def Pow10.square (p : Pow10) : Pow10 :=
  ⟨2 * p.exp, p.val * p.val, by rw [p.val_eq, Nat.two_mul, Nat.pow_add]⟩

/-- The powers `p`, `p^2`, `p^4` and so on that are at most `n`, the largest
first, before `ps`. -/
def powers (n : Nat) (p : Pow10) (ps : List Pow10) : List Pow10 :=
  if _h : p.val ≤ n ∧ 1 < p.val then powers n p.square (p :: ps) else ps
termination_by n + 1 - p.val
decreasing_by
  have : p.val < p.val * p.val := Nat.lt_mul_self_iff.mpr _h.2
  simp only [Pow10.square]
  omega

/-- Appends the `w` lowest digits of `n` to `acc`. It splits them at the
first power of `ps` with fewer digits than `w`, and writes each part with
the powers after it; with none, it lists them with `digitsOnto`. -/
def pushLow (acc : String) (w n : Nat) : List Pow10 → String
  | [] => acc ++ String.ofList (digitsOnto w n [])
  | p :: ps =>
    if p.exp < w then
      let q := n / p.val
      pushLow (pushLow acc (w - p.exp) q ps) p.exp (n - p.val * q) ps
    else pushLow acc w n ps

/-- Appends the digits of `n` to `acc`. It splits them at the first power of
`ps` that is at most `n`: it writes the quotient with the powers after it,
then the remainder with its leading zeros. With none, it writes `n` with
`Nat.repr`. -/
def pushNat (acc : String) (n : Nat) : List Pow10 → String
  | [] => acc ++ n.repr
  | p :: ps =>
    let q := n / p.val
    if q = 0 then pushNat acc n ps
    else pushLow (pushNat acc q ps) p.exp (n - p.val * q) ps

/-- Appends the digits of `n` to `acc`, splitting them at `10^18` and its
squares. -/
def appendNat (acc : String) (n : Nat) : String := pushNat acc n (powers n pow18 [])

/-- An integer in text, as `printInt` writes it. -/
def printDecimal : Int → String
  | .ofNat n => appendNat "" n
  | .negSucc n => appendNat "-" (n + 1)

theorem digitsOnto_eq (k n : Nat) (l : List Char) : digitsOnto k n l = lowDigits k n ++ l := by
  induction k generalizing n l with
  | zero => rfl
  | succ k ih => simp [digitsOnto, lowDigits, ih]

/-- A number's digits are those of its quotient by `10 ^ k`, then its `k`
lowest digits, when it has more than `k`. -/
theorem toDigits_eq_append {k n : Nat} (h : 10 ^ k ≤ n) :
    Nat.toDigits 10 n = Nat.toDigits 10 (n / 10 ^ k) ++ lowDigits k n := by
  induction k generalizing n with
  | zero => simp [lowDigits]
  | succ k ih =>
    have h10 : 10 ≤ n := Nat.le_trans (Nat.le_trans (by decide)
      (Nat.pow_le_pow_right (by decide) (Nat.succ_pos k))) h
    have hk : 10 ^ k ≤ n / 10 :=
      (Nat.le_div_iff_mul_le (by decide)).mpr (by rw [← Nat.pow_succ]; exact h)
    rw [Nat.toDigits_of_base_le (by decide) h10, ih hk, lowDigits, Nat.div_div_eq_div_mul,
      ← Nat.pow_succ', List.append_assoc]

/-- The `a + b` lowest digits of a number are the `a` lowest of its quotient
by `10 ^ b`, then its `b` lowest. -/
theorem lowDigits_add (a b n : Nat) :
    lowDigits (a + b) n = lowDigits a (n / 10 ^ b) ++ lowDigits b n := by
  induction b generalizing n with
  | zero => simp [lowDigits]
  | succ b ih =>
    rw [← Nat.add_assoc, lowDigits, lowDigits, ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ',
      List.append_assoc]

/-- The `k` lowest digits of a number are those of its remainder by
`10 ^ k`. -/
theorem lowDigits_mod (k n : Nat) : lowDigits k (n % 10 ^ k) = lowDigits k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [lowDigits, lowDigits, Nat.pow_succ', Nat.mod_mul_right_div_self, ih,
      Nat.mod_mul_right_mod]

theorem toList_pushLow (acc : String) (w n : Nat) (ps : List Pow10) :
    (pushLow acc w n ps).toList = acc.toList ++ lowDigits w n := by
  induction ps generalizing acc w n with
  | nil => simp [pushLow, digitsOnto_eq]
  | cons p ps ih =>
    rw [pushLow]
    split
    · rename_i h
      rw [ih, ih, ← Nat.mod_eq_sub_mul_div, p.val_eq, lowDigits_mod, List.append_assoc,
        ← lowDigits_add, Nat.sub_add_cancel (Nat.le_of_lt h)]
    · exact ih acc w n

theorem toList_pushNat (acc : String) (n : Nat) (ps : List Pow10) :
    (pushNat acc n ps).toList = acc.toList ++ Nat.toDigits 10 n := by
  induction ps generalizing acc n with
  | nil => simp [pushNat]
  | cons p ps ih =>
    rw [pushNat]
    split
    · exact ih acc n
    · rename_i h
      have hn : 10 ^ p.exp ≤ n := by
        rw [← p.val_eq]
        exact Nat.le_of_not_lt fun hlt => h (Nat.div_eq_zero_iff.mpr (.inr hlt))
      rw [toList_pushLow, ih, ← Nat.mod_eq_sub_mul_div, p.val_eq, lowDigits_mod,
        List.append_assoc, ← toDigits_eq_append hn]

theorem appendNat_eq (acc : String) (n : Nat) : appendNat acc n = acc ++ n.repr := by
  apply String.ext
  simp [appendNat, toList_pushNat]

/-- `printDecimal` writes an integer as the spec's `printInt` does, so
`fir-ref` runs it in place of `printInt`. -/
@[csimp] theorem printInt_eq_printDecimal : @printInt = @printDecimal := by
  funext i
  cases i <;> simp [printInt, printDecimal, appendNat_eq, Int.toString_eq_repr, Int.repr]

end FirRef
