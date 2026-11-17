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
to `cells.py`'s catalog. `sitofp` and
`uitofp`, with `round(rne)`, have a third, with a cell from each width of the
side to each of its float formats (`cells.INT_TO_FLOAT`).
`fpext` and `fptrunc` have a fourth, with a cell for each ordered pair of two
float formats of the side, under the op that the pair takes
(`cells.FLOAT_CONVERSIONS`, `cells.conversion`). The catalog supplies the
same cells and inapplicable-pair blanks to enumeration and rendering;
`coverage.catalog_table` formats them without reconstructing pairs.
The differential side has `f32` and `f64`, which the backend
lowers, and the interpreter-only side `f16`, `bf16`, `f32`, `f64` and `f128`.
Passed and returned values are cells at each of these formats too. A later float
op adds its row to `AT_FORMAT` in `scripts/harness/cells.py`
(ADR-2026-11-03-0557).

The fast-math flags count one by one. Each float op but the constant has a cell
for each of `nnan`, `ninf` and `nsz` at each format of a side, beside its cells
without flags (`cells.FAST_MATH`, `cells.FLAGGED`). A test exercises the cell of
each flag it sets, and not the op's cell without flags. `contract` and `reassoc`
are not cells, since validation rejects them, and `cells.py` reports one as an
error. Integer ops keep one cell per flag set: none, `nuw`, `nsw` and
`nuw nsw`. The human ruled this on 2026-11-13, on #355 (ADR-2026-11-03-0557).
Float flags are independent, and the spec proves that dropping any one refines
the op, so a test with two flags checks nothing that two one-flag tests miss;
the integer ops have at most four flag sets, which are cells already. A test
that fills a flag's cell is one whose outcome depends on the flag: a NaN operand
or result for `nnan`, an infinity for `ninf`, a zero result for `nsz`. `fcmp
nsz` is the exception: its result is not a float, so the flag has no effect,
and its test pins that. Rejected: a cell for every flag set, about 1,200 more
cells, with the float tables on a page of their own past the file-size budget;
and no cells for flags, with a flagged test counting towards the op without
flags, which leaves no check that each flag's rule is tested.

## How a NaN result is judged

A float op whose result is a NaN chooses its sign and mantissa, and the
harness judges native code's NaN on the part of the set that `fir-ref`
lists when it tries a few NaNs (ADR-2026-11-16-0855, ADR-2026-11-16-1630).
The human ruled on 2026-11-16 (#219 Q1) that the harness judges NaN
results this way, with declared results as the fallback for a program that
computes on a NaN's bits, and that NaN tries count against the 16-bit
choice budget (#219 Q2).

- A differential test runs `fir-ref run --exhaustive --nans` with no NaN
  given, so a NaN choice tries the positive quiet NaN and costs no bit. A
  run with no NaN choice is `complete`, and is judged as any other
  ([testing-and-harness.md](testing-and-harness.md#differential-tests)).
- Otherwise each outcome listed is one of the set, so the set's rules
  apply to them, and a native result that refines one passes.
- When the native result refines none, `differential.py` runs `fir-ref`
  again with native code's NaNs as `--nans`, once for each list, and
  judges on what it lists then. `native_floats.nans` reads them: each
  float result that is a NaN, and each integer result whose bits are a NaN
  of a float format of its width, as a NaN that went through `bitcast` or
  memory is.
- Each NaN given costs bits at every NaN choice of a path: with one, 17 NaN
  choices on a path pass the budget. That run then proves nothing, so the
  test is invalid unless it declares its results.
- A result outside the list fails, and the failure says that `fir-ref` cut
  the NaN choices short.
- A test whose result integer ops compute from a NaN's bits declares its
  results, each with a witness. Against a part of the set, each listed
  outcome must be declared, and the 32 seeded runs must each give a
  declared result, as past the budget.
- A native result on poison's stand-ins that fails against a part of the
  set is rechecked as past the budget
  ([testing-and-harness.md](testing-and-harness.md#poison-arguments)):
  `fir-ref` runs on the failing vector, with the seeded runs, and UB or
  fuel exhausted there makes the test invalid.

The generated programs' float functions are judged the same way
([testing-and-harness-generated.md](testing-and-harness-generated.md#float-functions)).

The list misses a NaN whose bits integer ops change, hence the declared
fallback, and UB or a stuck path that only an untried NaN reaches. A pass
is still sound: the native result is in the set. Rejected: native code
first, with its NaNs always given, which charges the budget on runs that
pass with the quiet NaN.

## The exact-rational reference

`scripts/harness/float_ref.py` computes IEEE 754 results at any format
`float<e,m>` with exact rational arithmetic, rounding to nearest even, apart
from Lean's code. `float_cases.py` writes, from it, the known answers that check
Lean's float model at `f16`, `bf16`, `f128` and `float<2,1>`. Its tests, under
the `fir-harness-test` hook, check it against the host's binary16, binary32 and
binary64 arithmetic. The human ruled on 2026-11-11 (#229) that this generator
lives under `scripts/harness/`, with its tests under the existing
`fir-harness-test` hook, and no new hook or CI step.

It was written in the same effort as the `fir-ref` code it checks, so a
misreading of IEEE 754 shared by both would pass. It is a convenience: it
does not meet the human's criterion of an independent reference, which
TestFloat meets ([below](#the-testfloat-check); #177, 2026-11-11).

## The TestFloat check

The human ruled on 2026-11-10 (#229) that `fir-ref` is checked against
Berkeley TestFloat's vectors at `f16` and `f128`, and that `bf16` has a
named reference. On 2026-11-11 the human had the M1 review's actions put on
#229: `float_ref.py` does not meet this, and TestFloat is built or vendored at
pinned commits for CI (#177).

`scripts/harness/testfloat.py`, which `scripts/check-harness.sh` runs after
the harness under the `fir-harness` hook, fetches TestFloat 3 and SoftFloat
3 with git at the commits of `PINS`, builds `testfloat_gen` once into
`~/.cache/funk/testfloat/`, and runs it at level 1, rounding to nearest
even, at `f16`, `f32`, `f64` and `f128`. It checks every vector of `add`,
`sub`, `mul`, `div` and `sqrt`, of `eq`, `le` and `lt`, 46,464 of each
function of two operands, and every 131st of `mulAdd`'s 6,133,248, 46,819:
about 1.5 million vectors. The pins are TestFloat's last commit and
SoftFloat's last before its `bf16` work, both of 2025-03-07.

- A batch of 1,000 vectors is one function that `bitcast`s integer
  constants to the format, runs the op on them and `bitcast`s each result
  back, so the check compares bits. `fir-ref validate` must accept it, and
  `fir-ref run --exhaustive --nans` runs it with no NaN given, so a NaN
  result is the positive quiet NaN.
- The exception flags are ignored, since M1 has none. A NaN that TestFloat
  gives passes on any NaN, since fir's op gives any NaN
  (ADR-2026-11-09-1549); every other result passes only on its bits.
- `eq`, `le` and `lt` back ten predicates of `fcmp` by IEEE 754 section
  5.11: `oeq`, `ole`, `olt`, their negations `une`, `ugt` and `uge`, and
  with the operands swapped `oge`, `ogt`, `ult` and `ule`. TestFloat has no
  vectors for `one`, `ueq`, `ord` and `uno`, for `fneg` and `fabs`, or for
  the remainders, which stay on `float_ref.py`'s corpus.
- At `f32` and `f64` it checks Lean's model apart from the backend; the
  corpus compares native code with `fir-ref`.
- It exits with 1 when a vector fails, and with 2 when TestFloat cannot be
  fetched or built or `fir-ref` gives no result for a batch, so a missing
  compiler or network fails the hook.

`bf16`, which TestFloat lacks, is checked against TestFloat's `f32`
vectors whose operands are all `bf16` values, the `f32` values with 16 low
zero bits: 589 for each function of two operands, 60 of `sqrt` and 14,165
of `mulAdd`. The arithmetic is generated rounding to odd, `-rodd`, and its
result is rounded once more, to nearest even at `bf16`; rounding to odd
with at least two more bits, then to nearest, is correctly rounded (Boldo
and Melquiond, IEEE Trans. Computers 57(4), 2008), and `f32` has 16 more
at every exponent. A comparison needs no rounding. These operands target
`f32`'s edges, not `bf16`'s ties, which the corpus's hard inputs target.
Rejected: SoftFloat's own `bf16` routines, new in October 2026, for which
`testfloat_gen` writes no vectors; and rounding `f32`'s nearest-even
result again, which `test_testfloat.py` shows wrong on one `mulAdd`.

Rejected: committed vectors, about 700 KB for each function and format at
level 1, past the file-size budget, or a sample of them; and one corpus
test, so one `fir-ref` process, per vector. `test_testfloat.py`, under
`fir-harness-test`, tests the parts that need no TestFloat.

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
(ADR-2026-11-09-1549), so its interpreter-only test has a choice that names
the NaN: the quiet NaN, every bit set, or the signalling NaN with only the
lowest mantissa bit, in turn. At `f32` and `f64` it is a differential test
too, judged as [above](#how-a-nan-result-is-judged).
`test_float_arith_cases.py` checks that the committed files are what the
generator writes, and checks every expected result against `float_ref.py`
again. A new hard input reaches every format,
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
is interpreter-only with its expected result. From `f32` to `f64` and from
`f64` to `f32` every case is differential too. `test_float_convert_cases.py` checks that the
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

## The fast-math flag corpus

`scripts/harness/float_flag_cases.py` writes the modules and tests
`float-flags-FORMAT` of `tests/fir/canonical/`, at every aliased format: a
function for each float op and each flag, such as `@fadd_nnan`, which fills that
flag's cell (#242). Each function's cases decide the flag, beside one that does
not: under `nnan` a NaN operand and operands whose result is a NaN, such as
`inf - inf`, `0 / 0` or `sqrt(-1)`, give poison; under `ninf` an infinite
operand and a result that rounds to an infinity, such as `M + M` or `1 / 0`, give
poison; under `nsz` a zero result is either zero, with one interpreter-only test
for each choice of the sign bit. `fcmp` takes `uno` under `nnan`, `olt` under
`ninf` and `oeq` under `nsz`, whose cases show the flag has no effect there. Each
expected result is `float_ref.py`'s with the flag's rule applied, and
`test_float_flag_cases.py` checks the committed files, each expected result,
and that each flag decides a case of each op. At `f32` and `f64` each case is a
differential test too: native code ignores the flags, and its result refines
poison and either zero. `reject/float-flags.toml` holds the texts of the flags
that do not decode and those that validation rejects.

## A NaN through memory

`tests/fir/canonical/float-nan-memory` casts a NaN to the integer of its
width, stores it and loads it back, at `f32` and `f64` (#219): M1 has no
float loads or stores. A function that returns the whole integer is a
differential test on native code's NaN as above. One that returns the byte
holding the sign declares both bytes, each with a witness that chooses the
sign, since integer ops cut it from the NaN. The flag corpus has no NaN
result to compare: under `nnan` a NaN gives poison, and its cases under
`ninf` and `nsz` give none.
