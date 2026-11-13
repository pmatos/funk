import Fir.Core.FloatOfInt

/-!
# Conversions between float formats

This section gives `fpext` and `fptrunc` their rule (ADR-2026-11-09-1549).
Each takes a value of `float<e,m>` and gives a value of `float<e',m'>`.
Lean's model has no conversion between formats, so fir defines it with
the model's own steps:

* `UnpackedFloat.unpack` reads the operand's bits, in the source format,
  as a signed zero, a finite number, a signed infinity or a NaN;
* a finite number, a mantissa and an exponent, goes to the target format
  by `UnpackedFloat.round`, the model's rounding to nearest, ties to even,
  which every rounded op of the model ends with;
* `UnpackedFloat.pack` writes the result as bits of the target format,
  and gives an infinity of its sign when the rounded number is too large
  for it.

A zero and an infinity keep their sign, and a NaN is a NaN. So

* a number that the target format holds is that number: every value of
  `f32` is a value of `f64`, and `fpext` of the `f32` value `0.1` gives
  the `f64` value `13421773 * 2^-27`, not the `f64` nearest `0.1`;
* any other is rounded to nearest even: `fptrunc` of the `f64` value
  `1 + 2^-24`, halfway between the `f32` values `1` and `1 + 2^-23`, gives
  `1`, whose mantissa is even;
* a number too large for the target is an infinity of its sign, as IEEE
  754 rounds an overflow to nearest: `fptrunc` of the `f32` value `65520`
  to `f16`, whose largest finite value is `65504`, is `+∞`;
* a number too small for the target's smallest subnormal is a zero of its
  sign: `fptrunc` of the `f64` value `2^-150`, half of `f32`'s smallest
  subnormal, is `+0`, since the tie goes to the even zero.

The two ops share the rule and differ in the pairs of formats they take,
which validation checks (the human's ruling of 2026-11-12 on #354):
`fpext` takes a pair whose target has at least as many exponent bits and
as many mantissa bits as the source, so that it holds every value of the
source and never rounds, and `fptrunc`, which carries `round(rne)`, takes
every other pair of two formats.

The rule is fir's own in three places, as the float arithmetic's is: a
poison operand gives a poison result (ADR-2026-10-29-2006), a NaN gives any
NaN of the target format, as `anyNaN` chooses it (ADR-2026-11-09-1549), and
when either format is one that the model does not have, which validation
rejects, the result is such a NaN too, so that the rule is total. Neither
op is ever UB, and neither carries fast-math flags: the rule is the float
result with no flags.
-/

namespace Fir.Core

open Float.Model

/-- The model's number `u`, read in one format, as a number of the format
`g`: a finite number rounded into `g` by the model, to nearest even, and a
zero, an infinity or a NaN as it is. -/
def convertModel (g : Format) : UnpackedFloat → UnpackedFloat
  | .finite s mt ex _ => UnpackedFloat.round g s mt ex
  | u => u

/-- The bits `b` of the format `f` converted to the format `g`, as the
model reads, rounds and writes them; a NaN as the model's one NaN. -/
def convertBits (f g : Format) (b : BitVec f.numBits) : BitVec g.numBits :=
  UnpackedFloat.pack g (convertModel g (UnpackedFloat.unpack f b))

/-- The rule of `fpext` and `fptrunc`, from `float<e,m>` to `float<e',m'>`:
the operand's number in the model, rounded into the target format, or any
NaN when it is a NaN, and poison when the operand is poison. -/
def convertFloat {μ : Type → Type} [Monad μ] [MonadChoice μ] (e m e' m' : Nat) :
    PoisonOr (BitVec (floatWidth e m)) → μ (PoisonOr (BitVec (floatWidth e' m')))
  | .value a => floatResult {} e' m' [] fun g _ =>
    if h : 2 ≤ e ∧ 0 < m then
      convertModel g
        (UnpackedFloat.unpack
          { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 } a)
    else .notANumber
  | .poison => pure .poison

/-- The model's rounding of a finite number never gives a NaN. -/
theorem round_isNaN (f : Format) (s : UnpackedFloat.Sign) (mt : Nat) (ex : Int) :
    (UnpackedFloat.round f s mt ex).isNaN = false :=
  roundWithAccuracy_isNaN ..

/-- A number that is not a NaN is not a NaN in any other format. -/
theorem convertModel_isNaN (g : Format) (u : UnpackedFloat) :
    (convertModel g u).isNaN = u.isNaN := by
  cases u with
  | finite s mt ex _ => exact round_isNaN g s mt ex
  | _ => rfl

/-- At two formats that the model has, the rule on a value that is not a
NaN gives the bits of its number rounded into the target, and chooses
nothing. -/
theorem convertFloat_valid {μ : Type → Type} [Monad μ] [MonadChoice μ] {e m e' m' : Nat}
    (h : 2 ≤ e ∧ 0 < m) (h' : 2 ≤ e' ∧ 0 < m') (a : BitVec (floatWidth e m))
    (hn : (UnpackedFloat.unpack
      { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 } a).isNaN =
        false) :
    convertFloat (μ := μ) e m e' m' (.value a) =
      pure (.value (convertBits
        { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }
        { exponentBits := e', mantissaBitsWithoutImplicit := m', he := h'.1, hm := h'.2 } a)) := by
  simp only [convertFloat, floatResult, h, h', and_self, ↓reduceDIte, convertModel_isNaN, hn,
    operandsBreak_nil, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! # Tests

`FirTest.FloatConvert` runs both ops on the boundary values of each pair of
formats. These check the rule's steps on a few of them.
-/

-- `f32`'s `0.1` is `f64`'s `0x3fb99999a0000000`, exactly, and back.
#guard (convertBits Format.binary32 Format.binary64 0x3dcccccd).toNat == 0x3fb99999a0000000
#guard (convertBits Format.binary64 Format.binary32 0x3fb99999a0000000).toNat == 0x3dcccccd
-- `1 + 2^-24` is halfway between `f32`'s `1` and `1 + 2^-23` and goes to
-- `1`; `1 + 3 * 2^-24` goes up, to `1 + 2^-22`.
#guard (convertBits Format.binary64 Format.binary32 0x3ff0000010000000).toNat == 0x3f800000
#guard (convertBits Format.binary64 Format.binary32 0x3ff0000030000000).toNat == 0x3f800002
-- `f32`'s smallest subnormal, `2^-149`, is a normal `f64`, and back.
#guard (convertBits Format.binary32 Format.binary64 0x00000001).toNat == 0x36a0000000000000
#guard (convertBits Format.binary64 Format.binary32 0x36a0000000000000).toNat == 0x00000001
-- `2^-150` is halfway between `+0` and `2^-149` and goes to `+0`; `-2^-150`
-- to `-0`.
#guard (convertBits Format.binary64 Format.binary32 0x3690000000000000).toNat == 0
#guard (convertBits Format.binary64 Format.binary32 0xb690000000000000).toNat == 0x80000000
-- `f64`'s largest finite value is `+∞` in `f32`; infinities and zeros keep
-- their sign.
#guard (convertBits Format.binary64 Format.binary32 0x7fefffffffffffff).toNat == 0x7f800000
#guard (convertBits Format.binary32 Format.binary64 0xff800000).toNat == 0xfff0000000000000
#guard (convertBits Format.binary32 Format.binary64 0x80000000).toNat == 0x8000000000000000
-- At `f16`, `65519` rounds to the largest finite value, `65504`, and
-- `65520`, halfway to `2^16`, to `+∞`.
#guard (convertBits Format.binary32 { exponentBits := 5, mantissaBitsWithoutImplicit := 10 }
  0x477fef00).toNat == 0x7bff
#guard (convertBits Format.binary32 { exponentBits := 5, mantissaBitsWithoutImplicit := 10 }
  0x477ff000).toNat == 0x7c00
-- `bf16` to `f16`: `2^-25`, half of `f16`'s smallest subnormal, goes to
-- `+0`, and `3 * 2^-26` up to `2^-24`.
#guard (convertBits { exponentBits := 8, mantissaBitsWithoutImplicit := 7 }
  { exponentBits := 5, mantissaBitsWithoutImplicit := 10 } 0x3300).toNat == 0
#guard (convertBits { exponentBits := 8, mantissaBitsWithoutImplicit := 7 }
  { exponentBits := 5, mantissaBitsWithoutImplicit := 10 } 0x3340).toNat == 0x0001

end Fir.Core
