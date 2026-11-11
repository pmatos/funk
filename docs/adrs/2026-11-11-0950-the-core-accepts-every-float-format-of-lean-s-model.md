# The core accepts every float format of Lean's model, and validation rejects a smaller one

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1549 gives fir one family of float types, `float<e,m>`, with
`e` exponent bits and `m` explicit mantissa bits, and leaves formats that are
not IEEE-shaped to dialects. It does not say which `e` and `m` the core
accepts.

Stage 1 of [#229](https://github.com/pmatos/funk/issues/229) checked Lean's
float model at `f16`, `bf16`, `f128` and `float<2,1>`
(`lean/FirTest/FloatModel.lean`). The model's `Format` needs `e >= 2` and
`m >= 1`. With `m = 1` the one mantissa bit of a NaN is its quiet bit, so the
format has no signalling NaN. fir never tells signalling NaNs from quiet
ones: a NaN result is any NaN bit pattern. The human ruled on #229 on
2026-11-11 that the core accepts every format the model supports.

An integer type is at most 16,777,215 bits wide, and a wider one does not
decode (ADR-2026-11-03-1000).

## Decision

- **Bounds.** The core accepts `float<e,m>` with `e >= 2` and `m >= 1`.
- **Where a smaller format is rejected.** Validation rejects a format with
  fewer bits, as it rejects `i0`. Such a type still decodes, so the text
  reads it and the verifier names it.
- **The widest format.** A value of `float<e,m>` has `1 + e + m` bits. A
  format wider than 16,777,215 bits in all, the widest integer type, does
  not decode, as a wider `iN` does not.
- **Values.** A value of `float<e,m>` is its raw bit pattern, a vector of
  `1 + e + m` bits, or poison. Values refine as integers do: poison is
  refined by every value of the type, and a bit pattern only by itself. So
  two NaNs with different bits are different values. The choice of a NaN
  result's bits belongs to the ops, which later stages of #229 add.

## Consequences

- `float<2,1>`, the smallest format, is a valid type, and the corpus checks
  it.
- The spec needs no format of its own beyond Lean's model: every core format
  is one of its `Format`s.
- A dialect that needs a format with fewer bits, or one that is not
  IEEE-shaped, brings its own type.
