# Current decisions: the float references

This page continues [testing-and-harness-floats.md](testing-and-harness-floats.md).
It says what holds today for the references that check `fir-ref`'s floating
point: `float_ref.py`, and Berkeley TestFloat. It is the record: when this
page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610).

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
`sub`, `mul`, `div`, `rem` and `sqrt`, of `eq`, `le` and `lt`, 46,464 of
each function of two operands, and every 131st of `mulAdd`'s 6,133,248, 46,819:
about 1.7 million vectors. The pins are TestFloat's last commit and
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
  vectors for `one`, `ueq`, `ord` and `uno`, or for `fneg` and `fabs`, which
  stay on `float_ref.py`'s corpus.
- TestFloat's `rem` is IEEE 754's remainder, `frem` (#430). It has no
  `fmod`, which stays on the arithmetic corpus's `float-rem-FORMAT`
  ([testing-and-harness-floats.md](testing-and-harness-floats.md#the-arithmetic-corpus)).
- At `f32` and `f64` it checks Lean's model apart from the backend; the
  corpus compares native code with `fir-ref`.
- It exits with 1 when a vector fails, and with 2 when TestFloat cannot be
  fetched or built or `fir-ref` gives no result for a batch, so a missing
  `gcc` or network fails the hook. A fetch is tried five times, 10 s apart.

`bf16`, which TestFloat lacks, is checked against TestFloat's `f32`
vectors whose operands are all `bf16` values, the `f32` values with 16 low
zero bits: 589 for each function of two operands, 60 of `sqrt` and 14,165
of `mulAdd`. The arithmetic is generated rounding to odd, `-rodd`, and its
result is rounded once more, to nearest even at `bf16`; rounding to odd
with at least two more bits, then to nearest, is correctly rounded (Boldo
and Melquiond, IEEE Trans. Computers 57(4), 2008), and `f32` has 16 more
at every exponent. A comparison needs no rounding, and neither does
`rem`: a remainder is exact, and `bf16` has `f32`'s exponents, so the
remainder of two `bf16` values is a `bf16` value. Its vectors are
generated to nearest even, and each result is read as it is; one that is
not a `bf16` value is an error, so the check would report it rather than
round it. `test_testfloat.py` checks the claim on `float_ref.py`.
These operands target
`f32`'s edges, not `bf16`'s ties, which the corpus's hard inputs target.
Rejected: SoftFloat's own `bf16` routines, new in October 2026, for which
`testfloat_gen` writes no vectors; and rounding `f32`'s nearest-even
result again, which `test_testfloat.py` shows wrong on one `mulAdd`.

Rejected: committed vectors, about 700 KB for each function and format at
level 1, past the file-size budget, or a sample of them; and one corpus
test, so one `fir-ref` process, per vector. `test_testfloat.py`, under
`fir-harness-test`, tests the parts that need no TestFloat.
