# The float arithmetic corpus is generated from the exact-rational reference

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

#229 asks for a fixed set of hard float inputs for every op: results
halfway between two floats, subnormals, `-0`, overflow to infinity and NaN
operands. `scripts/harness/float_ref.py` computes IEEE 754 results with
exact rational arithmetic, apart from Lean, and `float_cases.py` already
lists the hard inputs of each operation. A NaN result is any NaN
(ADR-2026-11-11-1800), and #219 decides how the harness judges one. Each
float op is a cell at each float format of a side (ADR-2026-11-11-1141).

## Decision

- `scripts/harness/float_arith_cases.py` writes the modules and tests
  `float-binary-FORMAT` and `float-unary-fma-FORMAT` of
  `tests/fir/canonical/`, at `f16`, `bf16`, `f32`, `f64` and `f128`, from
  the hard inputs of `float_cases.hard_cases`, with each case of `fsub`
  and `fdiv` also in the other operand order, and one poison operand per
  op. Each expected result is `float_ref.py`'s.
- A result that is not a NaN is a differential test at `f32` and `f64`,
  and an interpreter-only test with that result at every format.
- A NaN result is an interpreter-only test with a choice that names the
  NaN: the quiet NaN, every bit set, or the signalling NaN with only the
  lowest mantissa bit, in turn. No native NaN result is compared until
  #219.
- `test_float_arith_cases.py`, under the `fir-harness-test` hook, checks
  that the committed files are what the generator writes, and checks
  every expected result against `float_ref.py` again.

## Consequences

- Each new hard input reaches every format, both tools and the coverage
  matrix by running the generator.
- The NaN cases are left to #219: native code on them, and `fir-ref`'s
  exhaustive and sampled runs over the NaN choice.
