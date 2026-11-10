/-!
The check that Lean's float model works at formats other than binary32 and
binary64, before fir's spec builds on it (ADR-2026-11-09-1549; the human's
ruling of 2026-11-10 on #229). The model is `Float.Model.UnpackedFloat` in
Lean v4.35.0 (`src/Init/Data/Float/Model/`): each operation takes a
`Format`, an exponent width and a mantissa width, unpacks bit patterns,
computes and rounds to nearest even, and packs the result.

This module runs each operation that #229 builds on, for the format
`float<e,m>` with `e` exponent bits and `m` explicit mantissa bits: unpack
and pack, `add`, `sub`, `mul`, `div`, `fma`, `sqrt`, `neg`, `abs` and
`compare`. It checks them on every input at
`float<2,1>`, the smallest format the model accepts, below, and
`FirTest.FloatModelFma` checks `fma` there. The modules
`FirTest.FloatModelF16`, `FirTest.FloatModelBf16` and
`FirTest.FloatModelF128` check them on the hard inputs at `f16`, `bf16`
and `f128`.

Every expected bit pattern was computed apart from Lean's code, with exact
rational arithmetic. A finite operand is the rational number it encodes. A
finite nonzero result `x` is rounded at the quantum `q = 2^(k - m)`, where
`k` is the larger of `⌊log₂ |x|⌋` and the smallest normal exponent: `x/q`
goes to the nearest integer, a tie to the even one, and a result whose
magnitude reaches `2^(emax + 1)` is an infinity. A square root takes the
integer square root of `x/q²` and compares `x/q²` with the square of the
midpoint. The special cases (zeros and their signs, infinities, NaNs) follow
IEEE 754 §6 and §7, and every NaN result is the model's canonical NaN. That
reference agrees with the host's binary16, binary32 and binary64 arithmetic,
and with its binary64 `fma`, on every special value and on random inputs.

What the check found:

* Every operation gives the IEEE 754 result, rounded to nearest even, at
  each format checked, apart from the bits of a NaN below. The model has
  no case for binary32 or binary64: each operation is written once, for
  any `Format`.
* `Format` requires at least 2 exponent bits and 1 explicit mantissa bit,
  so fir must reject any `float<e,m>` with fewer. With `m = 1` the one
  mantissa bit of a NaN is its quiet bit, so `float<e,1>`, `float<2,1>`
  here included, has no signalling NaN, which IEEE 754 §3.4 encodes with
  that bit clear and another set.
* The model has one NaN, with no payload and no sign. `unpack` forgets a
  NaN's payload and sign, and `pack` writes the canonical NaN: the
  positive quiet NaN whose mantissa has only its top bit set. So `neg`
  and `abs` of a NaN give the canonical NaN, where IEEE 754's `negate` and
  `abs` would flip or clear the NaN's sign bit. fir lets a NaN result be
  any NaN bit pattern (ADR-2026-11-09-1549), which allows both. Unpacking
  and packing a NaN loses its payload, so a fir constant must keep its
  bits rather than go through the model.
* `compare` needs its operands in canonical form, and `unpack` gives that.
* The model has no remainder, so #229 does not build `frem`. It has no
  conversion between formats either, which ADR-2026-11-09-1549 already
  leaves to the spec.
* `UnpackedFloat.ofScientific`, which reads a decimal `m * 10^e`, is wrong
  at some formats: it returns `+0` whenever `e < -(2^E + log₂ m)`, for `E`
  exponent bits, whatever the mantissa width. At `float<2,100>`, whose
  smallest subnormal is `2^-100`, it reads `10^-5` as `+0`; the last case
  below pins that. #229 does not use it, since a constant is a bit
  pattern, and at `f16`, `bf16`, `f32`, `f64` and `f128` the cut-off lies
  below half the smallest subnormal.
* Rounding a result far below the format's range shifts its mantissa
  right one bit at a time, and `add`, `sub` and `fma` align operands with
  far-apart exponents exactly. At `f128` that is tens of thousands of
  bits, as in the product of two subnormals. The cases here run in well
  under a second, and the shift compiles to a loop (the `@[csimp]` lemma
  `Nat.repeat_eq_repeatTR`), so it takes no stack per bit.
-/

namespace FirTest.FloatModel

open Float.Model

/-- The format `float<e,m>`, with `e` exponent bits and `m` explicit mantissa
bits, as a `Format` of Lean's model. -/
def fmt (e m : Nat) (he : 2 ≤ e := by decide) (hm : 0 < m := by decide) : Format where
  mantissaBitsWithoutImplicit := m
  hm := hm
  exponentBits := e
  he := he

/-- `f16`, IEEE binary16. -/
abbrev f16 : Format := fmt 5 10

/-- `bf16`, bfloat16. -/
abbrev bf16 : Format := fmt 8 7

/-- `f128`, IEEE binary128. -/
abbrev f128 : Format := fmt 15 112

/-- `float<2,1>`, the smallest format the model accepts. -/
abbrev tiny : Format := fmt 2 1

/-- The model's reading of the bit pattern `a` of format `f`. -/
def un (f : Format) (a : Nat) : UnpackedFloat :=
  UnpackedFloat.unpack f (BitVec.ofNat f.numBits a)

/-- The bit pattern of `x`, packed in format `f`. -/
def pk (f : Format) (x : UnpackedFloat) : Nat :=
  (UnpackedFloat.pack f x).toNat

/-- `a + b` in format `f`. -/
def fadd (f : Format) (a b : Nat) : Nat := pk f (UnpackedFloat.add f (un f a) (un f b))

/-- `a - b` in format `f`. -/
def fsub (f : Format) (a b : Nat) : Nat := pk f (UnpackedFloat.sub f (un f a) (un f b))

/-- `a * b` in format `f`. -/
def fmul (f : Format) (a b : Nat) : Nat := pk f (UnpackedFloat.mul f (un f a) (un f b))

/-- `a / b` in format `f`. -/
def fdiv (f : Format) (a b : Nat) : Nat := pk f (UnpackedFloat.div f (un f a) (un f b))

/-- `a * b + c` with one rounding, in format `f`. -/
def ffma (f : Format) (a b c : Nat) : Nat :=
  pk f (UnpackedFloat.fma f (un f a) (un f b) (un f c))

/-- The square root of `a` in format `f`. -/
def fsqrt (f : Format) (a : Nat) : Nat := pk f (UnpackedFloat.sqrt f (un f a))

/-- `-a` in format `f`. -/
def fneg (f : Format) (a : Nat) : Nat := pk f (un f a).neg

/-- `|a|` in format `f`. -/
def fabs (f : Format) (a : Nat) : Nat := pk f (un f a).abs

/-- `a` unpacked and packed again: its bits, unless it is a NaN. -/
def fbits (f : Format) (a : Nat) : Nat := pk f (un f a)

/-- How `a` and `b` compare in format `f`: `none` when they are unordered. -/
def fcmp (f : Format) (a b : Nat) : Option Ordering := (un f a).compare (un f b)

/-! # Every input at `float<2,1>`

`float<2,1>` has 16 bit patterns, written below as the numbers 0 to 15.
0 to 5 are `+0`, `0.5` (the one subnormal), `1`, `1.5`, `2` and `3`;
6 is `+inf` and 7 is the canonical NaN. 8 to 15 are the same with the
sign bit set, so 15 is a NaN with its sign set. Each row below is one
first operand `a`, in order from 0 to 15, and its column is the second
operand `b`. The largest finite value is 3, so a result of 3.5 or more
overflows: 3.5 is a tie between 3 and 4, and 4 has the even mantissa.
`FirTest.FloatModelFma` checks `fma` on every triple. -/

/-- The results of `g` on each of the 16 bit patterns. -/
def row (g : Nat → Nat) : List Nat := (List.range 16).map g

/-- One row per first operand: the results of `g a b`. -/
def table (g : Nat → Nat → Nat) : List (List Nat) := (List.range 16).map fun a => row (g a)

/-- How a comparison prints in a table: `<`, `=`, `>`, or `u` for unordered. -/
def ordChar : Option Ordering → Char
  | none => 'u'
  | some .lt => '<'
  | some .eq => '='
  | some .gt => '>'

-- `a + b`, one row per `a`
#guard table (fadd tiny) == [
  [0, 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 7],
  [1, 2, 3, 4, 4, 6, 6, 7, 1, 0, 9, 10, 11, 12, 14, 7],
  [2, 3, 4, 4, 5, 6, 6, 7, 2, 1, 0, 9, 10, 12, 14, 7],
  [3, 4, 4, 5, 6, 6, 6, 7, 3, 2, 1, 0, 9, 11, 14, 7],
  [4, 4, 5, 6, 6, 6, 6, 7, 4, 3, 2, 1, 0, 10, 14, 7],
  [5, 6, 6, 6, 6, 6, 6, 7, 5, 4, 4, 3, 2, 0, 14, 7],
  [6, 6, 6, 6, 6, 6, 6, 7, 6, 6, 6, 6, 6, 6, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 7],
  [9, 0, 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 12, 14, 14, 7],
  [10, 9, 0, 1, 2, 4, 6, 7, 10, 11, 12, 12, 13, 14, 14, 7],
  [11, 10, 9, 0, 1, 3, 6, 7, 11, 12, 12, 13, 14, 14, 14, 7],
  [12, 11, 10, 9, 0, 2, 6, 7, 12, 12, 13, 14, 14, 14, 14, 7],
  [13, 12, 12, 11, 10, 0, 6, 7, 13, 14, 14, 14, 14, 14, 14, 7],
  [14, 14, 14, 14, 14, 14, 7, 7, 14, 14, 14, 14, 14, 14, 14, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]

-- `a - b`, one row per `a`
#guard table (fsub tiny) == [
  [0, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6, 7],
  [1, 0, 9, 10, 11, 12, 14, 7, 1, 2, 3, 4, 4, 6, 6, 7],
  [2, 1, 0, 9, 10, 12, 14, 7, 2, 3, 4, 4, 5, 6, 6, 7],
  [3, 2, 1, 0, 9, 11, 14, 7, 3, 4, 4, 5, 6, 6, 6, 7],
  [4, 3, 2, 1, 0, 10, 14, 7, 4, 4, 5, 6, 6, 6, 6, 7],
  [5, 4, 4, 3, 2, 0, 14, 7, 5, 6, 6, 6, 6, 6, 6, 7],
  [6, 6, 6, 6, 6, 6, 7, 7, 6, 6, 6, 6, 6, 6, 6, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [8, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6, 7],
  [9, 10, 11, 12, 12, 14, 14, 7, 9, 0, 1, 2, 3, 4, 6, 7],
  [10, 11, 12, 12, 13, 14, 14, 7, 10, 9, 0, 1, 2, 4, 6, 7],
  [11, 12, 12, 13, 14, 14, 14, 7, 11, 10, 9, 0, 1, 3, 6, 7],
  [12, 12, 13, 14, 14, 14, 14, 7, 12, 11, 10, 9, 0, 2, 6, 7],
  [13, 14, 14, 14, 14, 14, 14, 7, 13, 12, 12, 11, 10, 0, 6, 7],
  [14, 14, 14, 14, 14, 14, 14, 7, 14, 14, 14, 14, 14, 14, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]

-- `a * b`, one row per `a`
#guard table (fmul tiny) == [
  [0, 0, 0, 0, 0, 0, 7, 7, 8, 8, 8, 8, 8, 8, 7, 7],
  [0, 0, 1, 2, 2, 3, 6, 7, 8, 8, 9, 10, 10, 11, 14, 7],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 7],
  [0, 2, 3, 4, 5, 6, 6, 7, 8, 10, 11, 12, 13, 14, 14, 7],
  [0, 2, 4, 5, 6, 6, 6, 7, 8, 10, 12, 13, 14, 14, 14, 7],
  [0, 3, 5, 6, 6, 6, 6, 7, 8, 11, 13, 14, 14, 14, 14, 7],
  [7, 6, 6, 6, 6, 6, 6, 7, 7, 14, 14, 14, 14, 14, 14, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [8, 8, 8, 8, 8, 8, 7, 7, 0, 0, 0, 0, 0, 0, 7, 7],
  [8, 8, 9, 10, 10, 11, 14, 7, 0, 0, 1, 2, 2, 3, 6, 7],
  [8, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6, 7],
  [8, 10, 11, 12, 13, 14, 14, 7, 0, 2, 3, 4, 5, 6, 6, 7],
  [8, 10, 12, 13, 14, 14, 14, 7, 0, 2, 4, 5, 6, 6, 6, 7],
  [8, 11, 13, 14, 14, 14, 14, 7, 0, 3, 5, 6, 6, 6, 6, 7],
  [7, 14, 14, 14, 14, 14, 14, 7, 7, 6, 6, 6, 6, 6, 6, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]

-- `a / b`, one row per `a`
#guard table (fdiv tiny) == [
  [7, 0, 0, 0, 0, 0, 0, 7, 7, 8, 8, 8, 8, 8, 8, 7],
  [6, 2, 1, 1, 0, 0, 0, 7, 14, 10, 9, 9, 8, 8, 8, 7],
  [6, 4, 2, 1, 1, 1, 0, 7, 14, 12, 10, 9, 9, 9, 8, 7],
  [6, 5, 3, 2, 2, 1, 0, 7, 14, 13, 11, 10, 10, 9, 8, 7],
  [6, 6, 4, 3, 2, 1, 0, 7, 14, 14, 12, 11, 10, 9, 8, 7],
  [6, 6, 5, 4, 3, 2, 0, 7, 14, 14, 13, 12, 11, 10, 8, 7],
  [6, 6, 6, 6, 6, 6, 7, 7, 14, 14, 14, 14, 14, 14, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7],
  [7, 8, 8, 8, 8, 8, 8, 7, 7, 0, 0, 0, 0, 0, 0, 7],
  [14, 10, 9, 9, 8, 8, 8, 7, 6, 2, 1, 1, 0, 0, 0, 7],
  [14, 12, 10, 9, 9, 9, 8, 7, 6, 4, 2, 1, 1, 1, 0, 7],
  [14, 13, 11, 10, 10, 9, 8, 7, 6, 5, 3, 2, 2, 1, 0, 7],
  [14, 14, 12, 11, 10, 9, 8, 7, 6, 6, 4, 3, 2, 1, 0, 7],
  [14, 14, 13, 12, 11, 10, 8, 7, 6, 6, 5, 4, 3, 2, 0, 7],
  [14, 14, 14, 14, 14, 14, 7, 7, 6, 6, 6, 6, 6, 6, 7, 7],
  [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]

-- The square root, negation, absolute value and unpacking and packing of each
-- bit pattern from 0 to 15
#guard row (fsqrt tiny) == [0, 1, 2, 2, 3, 3, 6, 7, 8, 7, 7, 7, 7, 7, 7, 7]
#guard row (fneg tiny) == [8, 9, 10, 11, 12, 13, 14, 7, 0, 1, 2, 3, 4, 5, 6, 7]
#guard row (fabs tiny) == [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
#guard row (fbits tiny) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 7]

-- How `a` compares with `b`, one row per `a`
#guard (List.range 16).map (fun a => String.ofList ((List.range 16).map fun b =>
    ordChar (fcmp tiny a b))) == [
  "=<<<<<<u=>>>>>>u",
  ">=<<<<<u>>>>>>>u",
  ">>=<<<<u>>>>>>>u",
  ">>>=<<<u>>>>>>>u",
  ">>>>=<<u>>>>>>>u",
  ">>>>>=<u>>>>>>>u",
  ">>>>>>=u>>>>>>>u",
  "uuuuuuuuuuuuuuuu",
  "=<<<<<<u=>>>>>>u",
  "<<<<<<<u<=>>>>>u",
  "<<<<<<<u<<=>>>>u",
  "<<<<<<<u<<<=>>>u",
  "<<<<<<<u<<<<=>>u",
  "<<<<<<<u<<<<<=>u",
  "<<<<<<<u<<<<<<=u",
  "uuuuuuuuuuuuuuuu"]

/-! # A decimal that the model reads wrongly -/

-- `10^-5` at `float<2,100>` is far above the smallest subnormal, `2^-100`,
-- but the model reads it as `+0`. `10^-4` it reads as a number.
#guard pk (fmt 2 100) (UnpackedFloat.ofScientific (fmt 2 100) 1 (-5)) == 0
#guard pk (fmt 2 100) (UnpackedFloat.ofScientific (fmt 2 100) 1 (-4)) != 0

end FirTest.FloatModel
