# A generated coverage matrix counts the corpus's tests of each op instance, width and side, and a hook fails when it is stale or a cell has no test

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- **A cell** is an op instance of the core dialect at a width, on one side,
  differential or interpreter-only. An op instance is the op with its flag set,
  `exact` choice or `icmp` predicate. Width changes are cells for each pair of
  widths, `zext` and `sext` to a wider one and `trunc` to a narrower one, and
  passed and returned values (`br`, `cond_br`, `ret`, `call`, `func`) for none,
  one or several values.
- **Float flags count one by one.** A float op's fast-math flags are not part
  of its instance. Each float op but the constant has a cell for each of
  `nnan`, `ninf` and `nsz`, and a test fills the cell of each flag it sets; an
  integer op keeps one cell per flag set. `fcmp nsz` has no effect, since its
  result is not a float, so its cell holds a test that pins that.
- **Widths.** The differential side has `i1`, `i8`, `i16`, `i32`, `i64` and
  `i128`; the interpreter-only side adds `i7` and `i33`. The float ops, and
  values, are cells at each float format of a side: `f32` and `f64`
  differential, and `f16`, `bf16`, `f32`, `f64` and `f128` interpreter-only.
  Other widths and formats count towards no cell.
- **The count is static.** A test exercises each op of the function it runs and
  of every function that one calls, and the `func` cell of its results. Whoever
  fills a cell writes a test whose path runs the op and whose outcome depends on
  what it computes. `poison` is the exception: native code cannot tell it from
  `const 0`, so a differential test fills its cell by running it natively, and
  an interpreter-only test by observing the poison.
- **The check.** `scripts/harness/coverage.py` writes the matrix to
  `docs/coverage/README.md`. The `coverage-matrix` hook fails when it is stale
  or a cell has no test, and a unit test fails when `scripts/harness/cells.py`
  no longer follows the Lean op set. A new side or width edits this ADR and
  `cells.py`.

## Why

#23 asks for a coverage matrix of op, flag or predicate and width, for both
kinds of test, with every gap filled, and generated so that it stays current.
`fir-ref` reports a run's outcome, not the ops it ran, and a second interpreter
in Python would break S7, so the count reads the canonical text statically.

The human ruled on 2026-11-13 (#355) that float flags count per flag. They are
independent, and the spec proves that dropping any one refines the op, so a test
with two flags checks nothing that two one-flag tests miss. Per flag set, each
float op would have eight cells, and `fcmp` eight per predicate: about 1,200
more, past the file-size budget. Integer ops have four flag sets at most, so
their sets stay cells.

## Rejected alternatives

- **Cells by file name.** A name says what a module is for, not what its tests
  run.
- **A trace mode in `fir-ref`** to count the ops a run takes. It is a change to
  `fir-ref`'s command line of its own.
- **Width changes by source and target width apart.** It would hide a missing
  pair, such as `i7` to `i128`.
- **Every float flag set a cell**, about 1,200 more cells, with the float tables
  on a page of their own.
- **Float flags not cells**, a flagged test counting towards the op without
  flags: nothing would check that each flag's rule is tested.
