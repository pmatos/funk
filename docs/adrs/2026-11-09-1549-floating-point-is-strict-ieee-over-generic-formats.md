# Floating point is strict IEEE 754 over a generic family of formats, with nondeterministic NaNs and three fast-math flags

Status: accepted; refined by ADR-2026-11-11-0951, ADR-2026-11-11-1438 and
ADR-2026-11-11-1801
Tier: direction; area: semantics

## Decision

- **Formats.** One type family `float<e,m>`, with `e` exponent bits and `m`
  explicit mantissa bits, and the aliases `f16`, `bf16`, `f32`, `f64` and
  `f128`. The core accepts `e >= 2` and `m >= 1`, every format of Lean's
  float model, and validation rejects a smaller one. Formats that are not
  IEEE-shaped, such as fp8 e4m3fn, are left to dialects.
- **Semantics.** Strict IEEE 754. Denormals are honoured, and flush-to-zero
  is an explicit target attribute. A value is its bit pattern or poison.
- **NaNs.** When an op's IEEE result is a NaN, fir chooses any NaN bit
  pattern of the format: payload and sign are nondeterministic.
- **Rounding.** Every rounding op carries `round = rne`, the only value M1
  accepts.
- **Fast-math flags.** `nnan` and `ninf` make the result poison, and `nsz`
  makes a zero's sign a free choice. `contract` and `reassoc` are reserved
  words that the verifier rejects, left to M2's optimizer.
- **Built on Lean's model.** The spec defines fir's float ops, `fcmp` and the
  arithmetic among them, on Lean's float model, with a layer that adds the
  NaN choice, poison and the rejected formats. It writes no IEEE arithmetic
  of its own.
- **Backend.** The naive backend lowers `f32` and `f64` with SSE in M1, and
  reports any other format as a diagnostic.

[semantics-floats.md](../decisions/semantics-floats.md) states each rule and
the human's rulings: #203 (2026-11-09), #229's bounds (2026-11-11) and #310's
remainder (2026-11-12). The rounding-mode question on #229 is still open.

## Why

G0 asks for formats beyond binary32 and binary64, such as bf16 and fp8, so
NPU and TPU formats need no change to the core. Lean's model takes a format of
any width and rounds to nearest even, so the spec reuses it rather than writing
IEEE arithmetic from scratch. A rounding attribute keeps other modes possible
without a format break.

## Rejected alternatives

- **Only `f32` and `f64`, with all five flags.** Other formats would need a
  format change later, and two flags would ship without a sound meaning.
- **Strict `f32` and `f64` with no flags and no rounding attribute.** It drops
  the hook for other modes and fails G0's point on formats.
- **Require `m >= 2`.** It leaves `float<e,1>`, which Lean's model supports, to
  dialects, although fir never tells signalling NaNs from quiet ones.
