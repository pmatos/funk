/-!
# The remainders

This section defines the remainder that `frem` and `fmod` compute (#310;
the human's ruling of 2026-11-12). Both give `x - n * y` for operands `x`
and `y`, with an integer `n` near the quotient `x / y`:

* `frem` is IEEE 754's remainder (§5.3.1): `n` is `x / y` rounded to the
  nearest integer, a tie to the even one. So `5.5 frem 2.0` is `-0.5`. It
  follows ADR-2026-11-09-1549, strict IEEE 754.
* `fmod` is C's `fmod` (C17 §7.12.10.1): `n` is `x / y` truncated toward
  zero, so the result has the sign of `x`, and `5.5 fmod 2.0` is `1.5`.
  LLVM's `frem` is this op, so fir's `frem` is not LLVM's `frem`.

Neither rounds: the remainder of two finite floats is a multiple of the
smaller of their quanta, and no larger than `|y|`, so every format holds
it exactly. The special cases follow IEEE 754 for `frem` and C's Annex F
for `fmod`, which agree: `y = 0`, an infinite `x` or a NaN operand gives
a NaN; a finite `x` with an infinite `y` gives `x`; a zero `x` with a
nonzero `y` gives `x`; and a zero result has the sign of `x`.

# What comes from Lean's model, and what is fir's own

Lean's float model has no remainder, so fir defines it here, on the
model's numbers. From the model come the numbers, `UnpackedFloat`, which
`UnpackedFloat.unpack` reads from bits and `UnpackedFloat.pack` writes
back, and two of its steps: `UnpackedFloat.decreaseExponent`, which
writes a finite number at a smaller exponent, as the model's `add` does to
align its operands, and `UnpackedFloat.normalize`, which writes an
integer times a power of two as a number of the format. The arithmetic
of the remainder itself, the quotient and its rounding, is fir's own.
Float arithmetic then treats `frem` and `fmod` as it treats `fadd`: the
NaN of a result, poison and the formats the model does not have are its
rules (`Fir.Core.FloatArith`).
-/

namespace Fir.Core

open Float.Model

/-- The remainder of `x` by `y` at the format `f`: `x - n * y`, where the
integer `n` is `x / y` rounded to nearest, ties to even, when `nearest`
holds (IEEE 754's remainder, `frem`), and truncated toward zero when it
does not (C's `fmod`, `fmod`).

Two finite operands are written at the smaller of their exponents, as
the whole numbers `a` and `b` of that unit. With `q` and `r` the quotient
and remainder of `a / b`, the truncated remainder is `r`, and the nearest
one is `r - b` when `r` is more than half of `b`, or exactly half with an
odd `q`. Both are multiples of the unit, with the sign of `x` applied,
and `normalize` writes them in the format, which holds them exactly. A
zero result takes the sign of `x`. -/
def remainder (nearest : Bool) (f : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ | _, .notANumber | .infinity _, _ | _, .zero _ => .notANumber
  | x, .infinity _ => x
  | .zero s, _ => .zero s
  | .finite s mx ex _, .finite _ my ey _ =>
    let e := min ex ey
    let a := (UnpackedFloat.decreaseExponent mx ex e).1
    let b := (UnpackedFloat.decreaseExponent my ey e).1
    let r := a % b
    let up := nearest && (b < 2 * r || (2 * r = b && a / b % 2 = 1))
    UnpackedFloat.normalize f (s.apply (if up then (r : Int) - b else r)) e s

/-! # Tests

`FirTest.FloatRem` checks the remainder on the hard inputs at `f16`,
`bf16`, `f64` and `f128`, the examples of #310 among them, and on every
input at `float<2,1>`, against `scripts/harness/float_ref.py`. -/

end Fir.Core
