# Current decisions: testing floating point

This page continues [testing-and-harness.md](testing-and-harness.md). It says
what holds today for how the corpus and the coverage matrix test #229's
floating point. It is the record: when this page and an ADR disagree, the page
wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## The coverage matrix

The float ops have a table of their own: a float constant, `fcmp` with each
predicate, and each op of float arithmetic with its attribute, at each float
format of a side. The differential side has `f32` and `f64`, which the backend
lowers, and the interpreter-only side `f16`, `bf16`, `f32`, `f64` and `f128`.
Passed and returned values are cells at each of these formats too. A later float
op adds its row to `AT_FORMAT` in `scripts/harness/cells.py`
(ADR-2026-11-03-0557).

## The exact-rational reference

`scripts/harness/float_ref.py` computes IEEE 754 results at any format
`float<e,m>` with exact rational arithmetic, rounding to nearest even, apart
from Lean's code. `float_cases.py` writes, from it, the known answers that check
Lean's float model at `f16`, `bf16`, `f128` and `float<2,1>`. Its tests, under
the `fir-harness-test` hook, check it against the host's binary16, binary32 and
binary64 arithmetic. The human ruled on 2026-11-11 (#229) that this generator
lives under `scripts/harness/`, with its tests under the existing
`fir-harness-test` hook, and no new hook or CI step.

## The arithmetic corpus

`scripts/harness/float_arith_cases.py` writes the modules and tests
`float-binary-FORMAT` (`fadd`, `fsub`, `fmul`, `fdiv`) and
`float-unary-fma-FORMAT` (`fneg`, `fabs`, `sqrt`, `fma`) of
`tests/fir/canonical/`, at every aliased format. Its cases are the hard inputs
of `float_cases.hard_cases`: results halfway between two floats, subnormals,
`-0`, overflow to infinity and NaN operands, with `fsub` and `fdiv` in both
operand orders, and a poison operand per op. Each expected result is
`float_ref.py`'s.

A result that is not a NaN is a differential test at `f32` and `f64`, and an
interpreter-only test at every format. A NaN result is any NaN
(ADR-2026-11-11-1800), so its test is interpreter-only, with a choice that names
the NaN: the quiet NaN, every bit set, or the signalling NaN with only the
lowest mantissa bit, in turn. Native code is not compared on a NaN result until
#219 decides how one is judged. `test_float_arith_cases.py` checks that the
committed files are what the generator writes, and checks every expected
result against `float_ref.py` again. A new hard input reaches every format,
both tools and the coverage matrix by running the generator.

`crates/funk/tests/float_arith.rs` checks each op natively against the host's
arithmetic, and `fma`'s runtime routines also on random operands
([x86-64-backend-lowering.md](x86-64-backend-lowering.md#float-arithmetic)).
