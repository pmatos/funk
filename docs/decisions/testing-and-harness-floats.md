# Current decisions: testing floating point

This page continues [testing-and-harness.md](testing-and-harness.md). It says
what holds today for how the corpus and the coverage matrix test #229's
floating point. It is the record: when this page and an ADR disagree, the page
wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## The coverage matrix

The float ops have a table of their own: a float constant, `fcmp` with each
predicate, and each op of float arithmetic with its attribute, at each float
format of a side. The conversions have another, with a cell for each pair of
types that a conversion goes between: `bitcast` from each float format of the
side to the integer of its width, and back. A later conversion adds its pairs
to `cells.CONVERSIONS` and to `coverage.conversions_table`. `sitofp` and
`uitofp`, with `round(rne)`, have a third, with a cell from each width of the
side to each of its float formats (`cells.INT_TO_FLOAT`,
`coverage.int_to_float_table`). `fpext` and `fptrunc` have a fourth, with a
cell for each ordered pair of two float formats of the side, under the op
that the pair takes (`cells.FLOAT_CONVERSIONS`, `cells.conversion`,
`coverage.float_conversions_table`). The differential side has `f32` and `f64`, which the backend
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
`float-binary-FORMAT` (`fadd`, `fsub`, `fmul`, `fdiv`),
`float-unary-fma-FORMAT` (`fneg`, `fabs`, `sqrt`, `fma`) and
`float-rem-FORMAT` (`frem`, `fmod`) of `tests/fir/canonical/`, at every
aliased format. Its cases are the hard inputs of `float_cases.hard_cases`:
results halfway between two floats, subnormals, `-0`, overflow to infinity and
NaN operands, with `fsub` and `fdiv` in both operand orders, and a poison
operand per op. The remainders take theirs from `float_rem_cases.hard_cases`:
quotients halfway between two integers, operands far apart, subnormal
results, zeros of both signs, infinities and NaN operands, each in both
operand orders. Each expected result is `float_ref.py`'s, whose `remainder`
and `fmod` its tests check against the host's `math.remainder` and
`math.fmod`. `float_rem_cases.py` also writes `lean/FirTest/FloatRem.lean`,
the known answers of the spec's remainder at `f16`, `bf16`, `f64` and
`f128`, and on every input at `float<2,1>`.

A result that is not a NaN is a differential test at `f32` and `f64`, and an
interpreter-only test at every format. A NaN result is any NaN
(ADR-2026-11-09-1549), so its test is interpreter-only, with a choice that names
the NaN: the quiet NaN, every bit set, or the signalling NaN with only the
lowest mantissa bit, in turn. Native code is not compared on a NaN result until
#219 decides how one is judged. `test_float_arith_cases.py` checks that the
committed files are what the generator writes, and checks every expected
result against `float_ref.py` again. A new hard input reaches every format,
both tools and the coverage matrix by running the generator.

`crates/funk/tests/float_arith.rs` checks each op natively against the host's
arithmetic, and the runtime routines of `fma`, `frem` and `fmod` also on random
operands ([x86-64-backend-lowering-floats.md](x86-64-backend-lowering-floats.md#float-arithmetic)).
The host's `%` is C's `fmod`, and the test builds IEEE 754's remainder from it
exactly.

## The bit-cast corpus

`scripts/harness/float_bitcast_cases.py` writes `float-bitcast-FORMAT` of
`tests/fir/canonical/` at every aliased format: `@to_bits` casts a float to
the integer of its width and `@of_bits` casts back, on zeros of both signs,
the smallest and largest subnormals, the smallest normal, one, the largest
finite values, infinities, and NaNs, quiet and signalling, with payloads and
either sign, and on poison (#241). A bit cast chooses nothing, so each case,
a NaN's included, is differential at `f32` and `f64`, and interpreter-only at
every format with its operand's bits as the expected result; so is each
poison case, with poison expected.
`test_float_bitcast_cases.py` checks that the committed files are what the
generator writes, reads each expected result back with `float_text.py`, and
checks the edges against the host's `struct` at `f16`, `f32` and `f64`.

## The integer-to-float corpus

`scripts/harness/float_itofp_cases.py` writes `float-sitofp-FORMAT` and
`float-uitofp-FORMAT` of `tests/fir/canonical/` at every aliased format, with
`@si_iW` and `@ui_iW`, which convert an `iW` with `sitofp` and `uitofp`, at
each width the backend lowers, `i1` to `i128`, and `float-itofp-odd`, with the same conversions from
`i7` and `i33` to every format (#241). The cases are the boundary integers of
each width, read as signed or unsigned; the integers next to `2^p`, for the
format's precision `p`, below which every integer is exact; the integers
halfway between two floats there and at the top of the width's range, and the
ones next to them; and the integers on either side of the format's overflow,
where one rounds to the largest finite value and the next to infinity. Each
expected result is `float_ref.py`'s. A conversion never gives a NaN, so every
case of a width the backend lowers is differential at `f32` and `f64`, and every
case is interpreter-only with its expected result, poison included.
`test_float_itofp_cases.py` checks that the committed files are what the
generator writes, checks each expected result against the reference, and checks
the reference against the host's `struct` at `f16`, `f32` and `f64` on the
cases that binary64 holds exactly.
`crates/funk/tests/float_int_to_float.rs` checks every path of the backend's
lowering natively against the host's own conversion
([x86-64-backend-lowering-floats.md](x86-64-backend-lowering-floats.md#conversions-from-integers)).

## The format-conversion corpus

`scripts/harness/float_convert_cases.py` writes one module of
`tests/fir/canonical/` for each ordered pair of two aliased formats,
`float-OP-S-T`, whose function `@S_T` converts an `S` to a `T` with the op
the pair takes: nine with `fpext` and eleven with `fptrunc`, `bf16` to `f16`
and back among them (#241). The cases are the source's zeros, infinities,
`1`, smallest and largest subnormals, smallest normal and largest finite
value, and, where the source holds them, the target's edges: its largest
finite value and the value halfway past it, which goes to infinity; its
smallest subnormal and half of it, which goes to zero; the subnormals halfway
between two; and the values halfway between `1` and its neighbours, with the
source's values on either side of each halfway value. Each finite case comes
with its negation, and three NaNs and poison close each module. Each expected
result is `float_ref.convert`'s. A NaN operand gives any NaN, so its case is
interpreter-only with a choice, as in the arithmetic corpus; every other case
is interpreter-only with its expected result, and differential too from `f32`
to `f64` and from `f64` to `f32`. `test_float_convert_cases.py` checks that the
committed files are what the generator writes, checks each expected result
against the reference, checks the reference against the host's `struct`
between `f16`, `f32` and `f64`, and checks that the cases reach overflow,
underflow and ties. `crates/funk/tests/float_convert.rs` checks the backend's
`cvtss2sd` and `cvtsd2ss` natively against the host's `as`
([x86-64-backend-lowering-floats.md](x86-64-backend-lowering-floats.md#conversions-between-formats)).

## The float-to-integer corpus

`scripts/harness/float_fptoi_cases.py` writes `float-fptosi-FORMAT` and
`float-fptoui-FORMAT` of `tests/fir/canonical/` at every aliased format, with
`@s_iW` and `@u_iW`, which convert the format to an `iW` with `fptosi` and
`fptoui`, at each width the backend lowers, `i1` to `i128`, and
`float-fptosi-odd` and `float-fptoui-odd`, with the same conversions from every format to `i7` and
`i33` (#241). The cases are both zeros, the smallest subnormal, `0.5`, `1`,
`1.5`, `2.7` and `3`, the largest finite value, the infinities, and a NaN
with and without a payload, each of either sign, and at each end of the width's range the floats on
either side of where the truncated integer leaves it: the largest float below
`hi + 1`, which truncates into the range, and the smallest from it on, which
does not, and likewise at `lo - 1`, with `lo` itself for `fptosi`. Each
expected result is what `float_ref.py` decodes, truncated toward zero by
Python's `int`, or poison. A conversion chooses nothing, so every case of a
width the backend lowers is differential at `f32` and `f64`, where native code
refines poison with any value of the type (ADR-2026-10-30-2248), and every case
is interpreter-only with its expected result, poison included.
`test_float_fptoi_cases.py` checks that the committed files are what the
generator writes, checks each expected result against the reference, checks the
reference against the host's `struct` and `math.trunc` at `f16`, `f32` and
`f64`, and checks that the cases reach both ends of each range.
`crates/funk/tests/float_to_int.rs` checks every path of the backend's lowering
natively against the host's `trunc`, where the source gives an integer
([x86-64-backend-lowering-floats.md](x86-64-backend-lowering-floats.md#conversions-to-integers)).
