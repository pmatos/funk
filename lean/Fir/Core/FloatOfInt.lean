import Fir.Core.FloatArith

/-!
# Conversions from integers to floats

This section gives `sitofp` and `uitofp` their rule (ADR-2026-11-09-1549).
Each takes a value of `iN` and gives a value of `float<e,m>`, for any `N`
and any format:

* `sitofp` reads the operand's bits as a signed integer, in two's
  complement, so the `i8` value with every bit set is `-1`;
* `uitofp` reads them as an unsigned integer, so the same bits are `255`.

Lean's float model does the rest: `UnpackedFloat.ofInt` takes the integer
to a number of the model, rounded to nearest, ties to even, and
`UnpackedFloat.pack` writes it as bits, as for the float arithmetic. So

* an integer that the format holds exactly is that number: `sitofp` of the
  `i32` value `-3` to `f32` is `-3.0`;
* any other is rounded to nearest even: `16777217`, which is `2^24 + 1`,
  lies halfway between the `f32` values `2^24` and `2^24 + 2`, and goes to
  `2^24`, whose mantissa is even;
* an integer too large for the format is an infinity of its sign, as IEEE
  754 rounds an overflow to nearest: `uitofp` of the `i32` value `65520`
  to `f16`, whose largest finite value is `65504`, is `+∞`;
* zero is `+0`, for both ops.

The model never gives a NaN here: `ofInt` gives a zero or a finite number
(`ofInt_isNaN` below). So, at every format that validation accepts, the
rule gives one bit pattern and chooses nothing (`intToFloat_valid`).
Rounding to nearest even is the only mode M1 has, so each op carries
`round(rne)`, as the float arithmetic does, and the rule has no mode to
read.

The rule is fir's own in two places, as the float arithmetic's is: a
poison operand gives a poison result (ADR-2026-10-29-2006), and at a
format that the model does not have, which validation rejects, the result
is a NaN chosen as `anyNaN` chooses it, so that the rule is total. Neither
op is ever UB, and neither carries fast-math flags: the rule is the float
result with no flags.
-/

namespace Fir.Core

open Float.Model

/-- The integer that the bits `a` hold: in two's complement when `signed`,
and unsigned otherwise. -/
def intOfBits (signed : Bool) (a : BitVec n) : Int :=
  if signed then a.toInt else a.toNat

/-- The rule of `sitofp`, with `signed`, and of `uitofp`, from `iN` to
`float<e,m>`: the integer that the operand holds, rounded into the format
by the model, and poison when the operand is poison. -/
def intToFloat {μ : Type → Type} [Monad μ] [MonadChoice μ] (e m : Nat) (signed : Bool) :
    PoisonOr (BitVec n) → μ (PoisonOr (BitVec (floatWidth e m)))
  | .value a => floatResult {} e m [] fun f _ => UnpackedFloat.ofInt f (intOfBits signed a)
  | .poison => pure .poison

/-- The model's rounding of a finite number never gives a NaN. -/
theorem roundWithAccuracy_isNaN (f : Format) (s : UnpackedFloat.Sign) (mt : Nat) (ex : Int)
    (acc : UnpackedFloat.Accuracy) : (UnpackedFloat.roundWithAccuracy f s mt ex acc).isNaN = false := by
  simp only [UnpackedFloat.roundWithAccuracy]
  split <;> rfl

/-- The model's number of an integer is never a NaN. -/
theorem ofInt_isNaN (f : Format) (k : Int) : (UnpackedFloat.ofInt f k).isNaN = false := by
  simp only [UnpackedFloat.ofInt, UnpackedFloat.normalize]
  split
  · exact roundWithAccuracy_isNaN ..
  · rfl
  · exact roundWithAccuracy_isNaN ..

/-- At a format that the model has, the rule on a value gives the bits of
the model's number of the integer, and chooses nothing. -/
theorem intToFloat_valid {μ : Type → Type} [Monad μ] [MonadChoice μ] {e m : Nat}
    (h : 2 ≤ e ∧ 0 < m) (signed : Bool) (a : BitVec n) :
    intToFloat (μ := μ) e m signed (.value a) =
      pure (.value (UnpackedFloat.pack
        { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }
        (UnpackedFloat.ofInt
          { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }
          (intOfBits signed a)))) := by
  simp only [intToFloat, floatResult, h, and_self, ↓reduceDIte, ofInt_isNaN, operandsBreak_nil,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-! # Tests

`FirTest.FloatOfInt` runs both ops on the boundary integers of each
format. These check the model's rounding on a few of them.
-/

-- `2^24 + 1` is halfway between two `f32` values and goes to the even
-- one, `2^24`; `2^24 + 3` goes up, to `2^24 + 4`.
#guard (UnpackedFloat.pack Format.binary32 (UnpackedFloat.ofInt Format.binary32 16777217)).toNat ==
  0x4b800000
#guard (UnpackedFloat.pack Format.binary32 (UnpackedFloat.ofInt Format.binary32 16777219)).toNat ==
  0x4b800002
-- `-1` is `-1.0`, and `0` is `+0`.
#guard (UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofInt Format.binary64 (-1))).toNat ==
  0xbff0000000000000
#guard (UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofInt Format.binary64 0)).toNat == 0
-- At `f16`, `65519` rounds to the largest finite value, `65504`, and
-- `65520`, halfway to `2^16`, to `+∞`.
#guard (UnpackedFloat.pack { exponentBits := 5, mantissaBitsWithoutImplicit := 10 }
  (UnpackedFloat.ofInt { exponentBits := 5, mantissaBitsWithoutImplicit := 10 } 65519)).toNat == 0x7bff
#guard (UnpackedFloat.pack { exponentBits := 5, mantissaBitsWithoutImplicit := 10 }
  (UnpackedFloat.ofInt { exponentBits := 5, mantissaBitsWithoutImplicit := 10 } 65520)).toNat == 0x7c00
-- The bits of every `i8` read as signed and as unsigned.
#guard intOfBits true (0xff : BitVec 8) == -1 && intOfBits false (0xff : BitVec 8) == 255
#guard intOfBits true (BitVec.intMin 128) == -(2 ^ 127)

end Fir.Core
