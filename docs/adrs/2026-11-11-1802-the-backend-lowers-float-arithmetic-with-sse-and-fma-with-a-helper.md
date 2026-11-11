# The backend lowers float arithmetic with SSE2, and fma with a routine of a runtime helper

Status: accepted
Tier: implementation; area: x86-64-backend

## Context

The naive backend lowers `f32` and `f64` with SSE and reports every other
format as a diagnostic (ADR-2026-11-09-1549). Floats live in 8-byte slots
and pass in SSE registers (ADR-2026-11-11-1140). SSE2, which every x86-64
has, adds, subtracts, multiplies, divides and takes square roots of `f32`
and `f64`, rounded to nearest even by MXCSR's default mode. It has no fused
multiply-add: FMA3 is an extension that not every x86-64 has, and the
repo has no ruling on raising the instruction set. Division at `i128`
already calls a routine of a runtime helper that the module's object file
carries (ADR-2026-11-03-0414).

## Decision

- `fadd`, `fsub`, `fmul`, `fdiv` and `sqrt` are one SSE2 instruction each:
  `addss`, `subss`, `mulss`, `divss`, `sqrtss`, or the `sd` form at `f64`,
  on `%xmm0` and the second operand's slot. Nothing sets MXCSR's
  flush-to-zero or denormals-are-zero bits, so subnormals are honoured.
- `fneg` and `fabs` flip or clear the sign bit in `%rax` with `btcq` or
  `btrq`. That is IEEE 754's negate and abs, also on a NaN, which refines
  fir's any NaN (ADR-2026-11-11-1800).
- `fma` loads its operands into `%xmm0` to `%xmm2` and calls
  `__funk_rt_fmaf` or `__funk_rt_fma`, in `lower/fma.s`, which the module
  carries as it carries `div128.s`. Each is a System V function of three
  floats that uses only caller-saved registers and 16 bytes of stack, within
  the helper budget of ADR-2026-11-03-0415.
  - At `f32`, the product is exact in `f64`; the sum is rounded to odd in
    `f64`, toward zero with the last bit set when it was inexact, and then
    to nearest even in `f32`. Rounding to odd with two more bits rounds
    once (Boldo and Melquiond, 2008). MXCSR is restored after.
  - At `f64`, the routine computes `a * b + c` exactly in 128-bit integers
    and rounds it once, subnormals and overflow included. NaN and
    infinite operands, and zeros, take SSE's `a * b + c` or `a * b`, which
    is exact or correctly signed there.
- A NaN result is whatever the instruction or routine gives: any NaN is
  allowed.

## Alternatives

- **FMA3's `vfmadd`.** One instruction, but a program that uses it fails
  on an x86-64 without FMA3. Raising the instruction set needs a ruling.
- **`fma` from the C library.** Most modules link no C library
  (ADR-2026-11-10-1303).
- **Emulating `fma` at `f64` in double-double arithmetic.** It loses
  exactness near overflow and among subnormals, where the hard inputs
  are.

## Consequences

- Native code for float arithmetic needs only SSE2.
- `crates/funk/tests/float_arith.rs` checks every op against the host's
  IEEE 754 arithmetic, and `fma` also on random operands, cancelling
  ones, subnormal results and cases where rounding twice would tie.
