# Floating point is strict IEEE 754 over a generic family of formats, with nondeterministic NaNs and three fast-math flags

Status: accepted; refined by ADR-2026-11-11-0950, ADR-2026-11-11-0951,
ADR-2026-11-11-1138, ADR-2026-11-11-1139, ADR-2026-11-11-1140,
ADR-2026-11-11-1438, ADR-2026-11-11-1800, ADR-2026-11-11-1801 and
ADR-2026-11-11-1802
Tier: direction; area: semantics

## Context

This is decision S5 of the fir v0 decision record. The record proposed
strict IEEE 754, rounding to nearest even only, nondeterministic NaN
payloads and signs, honoured denormals with flush-to-zero as an explicit
target attribute, and fast-math as per-op flags (`nnan`, `ninf`, `nsz`,
`contract`, `reassoc`). It promised a hook: rounding is an op attribute, so
other modes can come back without a format break. G0
(ADR-2026-10-29-2016) asks for formats beyond binary32 and binary64, such as
bf16 and fp8.

Lean v4.35.0, which the repo pins, models `Float` and `Float32` explicitly
in its logic (`src/Init/Data/Float/Model/` of the Lean sources). Its
operations take a format of any exponent and mantissa width, round to
nearest even, and have one canonical NaN with no payload or sign. It ships
no lemmas, and leaves conversion between widths opaque. The human ruled on
[#203](https://github.com/pmatos/funk/issues/203) on 2026-11-09.

## Decision

- **Formats.** One type family `float<e,m>`, with `e` exponent bits and `m`
  explicit mantissa bits. The usual names are aliases: `f16`, `bf16`,
  `f32`, `f64` and `f128`. The spec and `fir-ref` handle every IEEE-shaped
  format. Formats that are not IEEE-shaped, such as fp8 e4m3fn, which has
  no infinities, are left to dialects.
- **Semantics.** Strict IEEE 754. Denormals are honoured. Flush-to-zero is
  an explicit target attribute.
- **NaNs.** When an op's IEEE result is a NaN, fir chooses any NaN bit
  pattern of the format: payload and sign are nondeterministic.
  [#219](https://github.com/pmatos/funk/issues/219) decides how `fir-ref`
  and the harness handle the choice.
- **Rounding.** Every rounding op carries `round = rne`. Round to nearest
  even is the only value M1 accepts.
- **Fast-math flags.**
  - `nnan`: a NaN operand or result makes the result poison.
  - `ninf`: an infinite operand or result makes the result poison.
  - `nsz`: the sign of a zero result is a free choice.
  - `contract` and `reassoc` are reserved words that the verifier rejects.
    They are permissions for passes, not meanings of an op, and M2's
    optimizer decides them.
- **Building on Lean.** The spec defines fir's float ops on Lean's model,
  with a layer that adds the NaN choice. It defines the conversions between
  widths itself. Facts it needs are proved here, or checked with `decide`
  and `bv_decide`. Before relying on the model, the implementation confirms
  that each operation works for a format other than binary32 and binary64.
- **Backend.** The naive backend lowers `f32` and `f64` with SSE in M1. It
  reports any other format as a diagnostic.

## Alternatives

- **Only `f32` and `f64`, with all five flags.** Other formats would need
  a format change later, and two flags would ship without a sound meaning.
- **Strict `f32` and `f64` with no flags and no rounding attribute.** It
  drops the promised hook and fails G0's point on formats.

## Consequences

- NPU and TPU formats need no change to the core.
- The spec reuses Lean's model and writes no IEEE arithmetic from scratch.
- A native result in a format the backend does not lower is judged by
  `fir-ref` alone.
