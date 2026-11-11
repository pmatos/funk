# Float arithmetic runs Lean's model, and a NaN result is any NaN, chosen by sign and mantissa

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1549 defines fir's float ops on Lean's float model, with a
layer that lets a NaN result be any NaN bit pattern. #229's stage 4 adds
the arithmetic: `fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `sqrt` and
`fma`. The model (`Float.Model.UnpackedFloat` in Lean v4.35.0) has each
of them, rounded to nearest even, and #229's first stage checked them at
`f16`, `bf16`, `f128` and `float<2,1>` (`FirTest.FloatModel`). The model
has one NaN, with no payload and no sign, so its `neg` and `abs` of a NaN
give that NaN. It has no remainder, so `frem` is not built. A run that
makes a choice is a tree of choices in `fir-ref`, as `freeze`'s is.

## Decision

- **Ops.** `fadd`, `fsub`, `fmul` and `fdiv` take two values of one float
  type, `fneg`, `fabs` and `sqrt` one, and `fma` three; each gives one
  value of that type. In the spec they are three op instances:
  `fbin o e m`, `funary o e m` and `fma e m`.
- **The model.** On defined operands, each op unpacks them with
  `UnpackedFloat.unpack`, runs the model's operation (`add`, `sub`, `mul`,
  `div`, `neg`, `abs`, `sqrt` or `fma`) and, when the result is not a NaN,
  packs it with `UnpackedFloat.pack`.
- **NaN results.** When the model's result is a NaN, the op chooses
  `m + 1` bits: the top one is the sign and the low `m` are the
  mantissa, with the exponent all ones. A mantissa of zeros would be an
  infinity, so it stands for the quiet NaN, with only the top mantissa bit
  set. So every NaN of the format may be the result, quiet or signalling,
  with any payload and either sign, and nothing else. The op chooses only
  when the result is a NaN, through the choice effect, as `freeze` does
  (`anyNaN` in `lean/Fir/Core/FloatArith.lean`).
- **`fneg` and `fabs`** go through the model too, so their result on a NaN
  is any NaN.
- **Poison and UB.** A poison operand gives a poison result. No op is ever
  UB: division by zero gives an infinity or a NaN, and M1 has no
  floating-point exceptions.
- **Effects.** Each op is pure. A NaN is a defined value, so on defined
  operands the result is defined. `mayPoison` comes with the fast-math
  flags (#242).
- **Formats the model does not have.** Validation rejects them
  (ADR-2026-11-11-0950). So that the rules are total, every result in
  such a format is a NaN chosen as above.

## Alternatives

- **`fneg` and `fabs` as bit operations,** flipping or clearing the sign
  bit, as IEEE 754 and LLVM define them. A NaN operand would then give one
  NaN, and the ops would be differential on NaNs today. ADR-2026-11-09-1549
  defines the float ops on the model, which gives any NaN, so this ADR
  keeps that; the bit operations refine it, and the backend uses them.
- **Choose all `1 + e + m` bits and keep them only when they are a NaN.**
  It needs a fallback for the bits that are not, and a choice of more
  bits, which exhaustive runs pay for.

## Consequences

- The spec builds every float op on the model and writes no IEEE
  arithmetic of its own; fir's own parts are the NaN choice, poison and
  the rejected formats, and the spec's section on float arithmetic lists
  them.
- `fir-ref run` gives one result, with no choice, for every result that
  is not a NaN, so `funk` and `fir-ref` compare those differentially. A
  NaN result needs a choice: scripted mode takes it with `--choices`, and
  exhaustive mode at `f32` and `f64` passes its 16-bit budget. #219 decides
  how `fir-ref` and the harness judge a NaN result.
