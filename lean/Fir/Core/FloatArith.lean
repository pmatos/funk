import Fir.Core.Values
import Fir.Core.Ops

/-!
# Float arithmetic

This section gives the float arithmetic its rules (ADR-2026-11-09-1549,
ADR-2026-11-11-1800): `fadd`, `fsub`, `fmul` and `fdiv` of two operands,
`fneg`, `fabs` and `sqrt` of one, and `fma` of three. Each takes and gives
values of one format `float<e,m>`. None is ever UB, and a poison operand
gives a poison result.

# What comes from Lean's model, and what is fir's own

Lean's float model (`Float.Model` in Lean v4.35.0) does the arithmetic.
From the model come:

* reading a bit pattern as a number: `UnpackedFloat.unpack` reads it as a
  signed zero, a finite number, a signed infinity or a NaN;
* the operations on numbers: `UnpackedFloat.add`, `sub`, `mul`, `div`,
  `fma` and `sqrt`, each rounded to nearest, ties to even, and `neg` and
  `abs`;
* writing a number that is not a NaN back as bits: `UnpackedFloat.pack`,
  which gives an infinity when the rounded number is too large for the
  format.

The model computes each operation once for every format, and the first
stage of #229 checked it at `f16`, `bf16`, `f128` and `float<2,1>` as well
as `f32` and `f64` (`FirTest.FloatModel`). Every rule here also holds the
model's choice of when a result is a NaN: `0/0`, `inf - inf`, `0 * inf`,
the square root of a number below zero, and every operation with a NaN
operand.

fir's own are:

* _The NaN of a result._ The model has one NaN, with no payload and no
  sign. When the model's result is a NaN, fir's result is any NaN of the
  format: the rule chooses a sign and the `m` bits of a mantissa, and
  gives the NaN with those bits. A mantissa of zeros would spell an
  infinity, so it stands for the quiet NaN, whose mantissa has only its
  top bit set. So every NaN of the format, quiet or signalling, with any
  payload and either sign, may be the result, and nothing else may
  (ADR-2026-11-09-1549). The rule chooses only when the result is a NaN,
  so every other result is one bit pattern.
* _`fneg` and `fabs` of a NaN._ They go through the model too, so the
  negation or the absolute value of a NaN is any NaN, not only the
  operand with its sign bit flipped or cleared.
* _The rounding attribute._ Every op that rounds, all but `fneg` and
  `fabs`, carries `round(rne)`, and round to nearest even is the only
  mode M1 has, so the rules have none to read.
* _Poison._ A poison operand gives a poison result
  (ADR-2026-10-30-0818); the model has no poison.
* _Formats the model does not have._ The model needs at least 2 exponent
  bits and 1 mantissa bit. Validation rejects every other format
  (ADR-2026-11-11-0950), so no valid program computes in one. So that the
  rules are still total, every result in such a format is a NaN chosen as
  above.
* _No exceptions, no flush to zero._ M1 has no floating-point exceptions
  and no flags to read them, and subnormal operands and results are
  honoured: flush to zero is a target attribute, which M1 does not have.

The model has no remainder, so fir has no `frem` (#229), and the
conversions between formats are left to a later ticket.
-/

namespace Fir.Core

open Float.Model

/-- The bits of the NaN of `float<e,m>` that the `m + 1` bits `c` choose:
its sign is the top bit of `c`, its exponent is all ones, and its
mantissa is the low `m` bits of `c`, or the quiet NaN's when those are all
zeros. -/
def nanBits (e m : Nat) (c : BitVec (m + 1)) : BitVec (floatWidth e m) :=
  let payload := c.toNat % 2 ^ m
  let mantissa := if payload = 0 then 2 ^ (m - 1) else payload
  .ofNat _ ((c.toNat / 2 ^ m) * 2 ^ (e + m) + (2 ^ e - 1) * 2 ^ m + mantissa)

/-- Any NaN of `float<e,m>`: the rule chooses its sign and mantissa. -/
def anyNaN {μ : Type → Type} [Monad μ] [MonadChoice μ] (e m : Nat) :
    μ (PoisonOr (BitVec (floatWidth e m))) := do
  let c ← MonadChoice.choose (m + 1)
  pure (.value (nanBits e m c))

/-- The result of a float op in `float<e,m>`, whose result in Lean's model
is `r f (unpack f)`, for the model's format `f` and its reading of bits:
the bits of that result, or any NaN when it is a NaN. In a format the
model does not have, any NaN. -/
def floatResult {μ : Type → Type} [Monad μ] [MonadChoice μ] (e m : Nat)
    (r : Format → (BitVec (floatWidth e m) → UnpackedFloat) → UnpackedFloat) :
    μ (PoisonOr (BitVec (floatWidth e m))) :=
  if h : 2 ≤ e ∧ 0 < m then
    let f : Format :=
      { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }
    let u := r f (UnpackedFloat.unpack f)
    if u.isNaN then anyNaN e m else pure (.value (UnpackedFloat.pack f u))
  else anyNaN e m

/-- What each float op of two operands computes in Lean's model. -/
def FBin.model : FBin → (f : Format) → UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .fadd => UnpackedFloat.add
  | .fsub => UnpackedFloat.sub
  | .fmul => UnpackedFloat.mul
  | .fdiv => UnpackedFloat.div

/-- What each float op of one operand computes in Lean's model. -/
def FUnary.model : FUnary → (f : Format) → UnpackedFloat → UnpackedFloat
  | .fneg => fun _ => UnpackedFloat.neg
  | .fabs => fun _ => UnpackedFloat.abs
  | .sqrt => UnpackedFloat.sqrt

/-- The rule of `fadd`, `fsub`, `fmul` and `fdiv` in `float<e,m>`: the
model's result, or any NaN when it is a NaN, and poison when either
operand is poison. -/
def fbinValues {μ : Type → Type} [Monad μ] [MonadChoice μ] (o : FBin) :
    PoisonOr (BitVec (floatWidth e m)) → PoisonOr (BitVec (floatWidth e m)) →
      μ (PoisonOr (BitVec (floatWidth e m)))
  | .value a, .value b => floatResult e m fun f un => o.model f (un a) (un b)
  | _, _ => pure .poison

/-- The rule of `fneg`, `fabs` and `sqrt` in `float<e,m>`: the model's
result, or any NaN when it is a NaN, and poison when the operand is
poison. -/
def funaryValue {μ : Type → Type} [Monad μ] [MonadChoice μ] (o : FUnary) :
    PoisonOr (BitVec (floatWidth e m)) → μ (PoisonOr (BitVec (floatWidth e m)))
  | .value a => floatResult e m fun f un => o.model f (un a)
  | .poison => pure .poison

/-- The rule of `fma` in `float<e,m>`: `a * b + c` with one rounding, in
the model, or any NaN when that is a NaN, and poison when any operand is
poison. -/
def fmaValues {μ : Type → Type} [Monad μ] [MonadChoice μ] :
    PoisonOr (BitVec (floatWidth e m)) → PoisonOr (BitVec (floatWidth e m)) →
      PoisonOr (BitVec (floatWidth e m)) → μ (PoisonOr (BitVec (floatWidth e m)))
  | .value a, .value b, .value c => floatResult e m fun f un => UnpackedFloat.fma f (un a) (un b) (un c)
  | _, _, _ => pure .poison

/-! # Tests

`FirTest.FloatArith` runs every op on the hard inputs of each format.
These check the NaN bits that a choice gives.
-/

-- At `f32`: a zero mantissa stands for the quiet NaN, of either sign; any
-- other mantissa is kept, a signalling NaN's included.
#guard nanBits 8 23 0 == 0x7fc00000 && nanBits 8 23 0x800000 == 0xffc00000
#guard nanBits 8 23 1 == 0x7f800001 && nanBits 8 23 0xffffff == 0xffffffff
-- At `float<2,1>`, whose NaNs are 7 and 15: the one mantissa bit is the
-- quiet bit.
#guard (List.range 4).map (fun c => (nanBits 2 1 (.ofNat 2 c)).toNat) == [7, 7, 15, 15]

end Fir.Core
