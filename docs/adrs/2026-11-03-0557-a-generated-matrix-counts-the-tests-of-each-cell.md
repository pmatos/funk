# A generated coverage matrix counts the corpus's tests of each op instance, width and side, and a hook fails when it is stale or a cell has no test

Status: accepted; refined by ADR-2026-11-03-1618

## Context

[#23](https://github.com/pmatos/funk/issues/23) asks for "a coverage
matrix of op × flag or predicate × width, for both differential and
interpreter-only tests", with every gap filled, which "also covers
functions and calls with zero, one and several results". A script must
generate it, so that it stays current. The epic's M0 op set is the core
dialect's `Op` in `lean/Fir/Core/Ops.lean`, and
`lean/Fir/Core/Text.lean` says which attributes each op takes. The
backend lowers `i1`, `i8`, `i16`, `i32`, `i64` and `i128` (S2), and the
epic asks for `i7` and `i33` in the interpreter-only tests. A test
without `expect` is differential, and one with `expect` is
interpreter-only (ADR-2026-10-30-2050). `fir-ref` reports a run's
outcome, not the ops it ran.

## Decision

- **A cell** is an op instance of the core dialect at a width, on one
  side, differential or interpreter-only:
  - `const`, `srem`, `urem`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`,
    `select` and `freeze` at each width. A constant's value is not part
    of its cell.
  - `add`, `sub` and `mul` with each flag set that `decodeWrap` reads:
    none, `nuw`, `nsw`, `nuw nsw`. `sdiv` and `udiv` with and without
    `exact` (`decodeExact`). `icmp` with each predicate of `Pred.all`.
    A flag that the spec does not give an op, such as `exact` on `srem`,
    is not a cell.
  - `zext` and `sext` from `iM` to `iN` for each pair of widths with
    `M < N`, and `trunc` for each pair with `N < M`.
  - Passed and returned values: `br`, and each successor of `cond_br`,
    passes nothing, or values of a width; `ret` returns no value, one
    value or several; a `call` gives no result, one or several; and so
    does `func`, the function that a test runs. One value or several is
    a cell at each width that one of the values has.
- **Widths.** The differential side has the backend's six widths. The
  interpreter-only side has those six and `i7` and `i33`. Ops at other
  widths, such as those of `widths.fir`, count towards no cell.
- **What a test exercises.** `scripts/harness/firtext.py` reads each
  canonical module with the text format's one grammar for every op. A
  test exercises the cell of each op of the function it runs and of
  every function that one calls, directly or through others, and the
  `func` cell of its function's results. This is static: a block that
  the test's arguments skip still counts. `fir-ref` gives no trace of
  the ops a run takes, and a second interpreter in Python would break
  S7. So whoever fills a cell writes a test whose path runs the op and
  whose outcome depends on what the op computes: a test that only passes
  poison into the op checks how poison goes through it, not the op. The
  count does not look at the outcome; the harness judges that.
- **The matrix.** `scripts/harness/coverage.py` counts, for each cell,
  the tests that exercise it, and writes the counts as Markdown to
  [`docs/coverage/README.md`](../coverage/README.md): for each side, a
  table of ops at a width, one of width changes and one of passed and
  returned values. It cannot live in `tests/fir/`, which holds only the
  corpus (ADR-2026-10-30-2050). Its size follows the cell set, not the
  number of tests: about 9,400 bytes. A new width or side that would
  take it past the file-size budget splits it by side into files of
  `docs/coverage/`.
- **The check.** The `coverage-matrix` pre-commit hook runs
  `coverage.py`, which fails when the committed matrix is not the one it
  makes, or when a cell has no test. `coverage.py --write` rewrites it.
  The unit tests run in the `fir-harness-test` hook, and one of them
  reads `Op.name`, `Pred.all`, `decodeWrap`, `decodeExact`, the arms
  of `Op.decode` and `Op.attrs`, and `plainBinOps` in `Text.lean`. It
  fails when the cell set no longer follows them, and so when an op
  that took no attribute is given one through an existing decoder, such
  as `exact` on `lshr`.

## Alternatives

- **Cells by file name.** A name says what a module is for, not what
  its tests run.
- **A trace mode in `fir-ref`** to count only the ops that a run takes.
  It is a change to `fir-ref`'s command line (ADR-2026-10-30-1425) of
  its own.
- **Width changes by source width and target width apart.** It would
  hide a missing pair, such as `i7` to `i128`.

## Consequences

- Adding or removing a test changes the counts, so a PR that changes
  the corpus regenerates the matrix, after merging `main` when `main`
  changed the corpus too.
- A new op, flag or predicate in the core dialect, or a flag on an op
  that had none, fails the unit tests until `scripts/harness/cells.py`
  has its cells, and then the hook until the corpus tests them.
- A new side or width is a change to this ADR and to `cells.py`.
