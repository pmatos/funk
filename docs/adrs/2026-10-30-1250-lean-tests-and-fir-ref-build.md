# fir's Lean code is tested by `#guard` checks and by `fir-ref` over the shared texts, and `fir-ref` is built by `build-spec.sh --lean`

Status: accepted

## Context

ADR-2026-10-29-2135 makes `lean/` the Lake package `fir`, with no
dependencies, built by `scripts/build-spec.sh` under two git guards. It
leaves to [#10](https://github.com/pmatos/funk/issues/10) how the Lean code
is tested and how the `fir-ref` executable is built.

Facts:

- `#guard` fails the build of its module when its check is false, so
  building a Lean library runs its checks.
- Tests that read files (the shared texts in `tests/fir/`, and the texts
  that Rust prints) need a program to run: elaboration-time I/O would depend
  on Lake's working directory, and would not test the binary that the
  harness of [#13](https://github.com/pmatos/funk/issues/13) runs.
- Every check lives in `.pre-commit-config.yaml`, and CI runs exactly that.
  The CI job already installs elan, the pinned Lean toolchain and the pinned
  Rust toolchain.
- Lean's runtime runs a program's `main` on a thread with a large stack
  (`LEAN_STACK_SIZE_KB` sets it). Measured on 2026-10-30, `fir-ref` parses
  texts nested 3,000,000 levels deep in attributes, and 1,000,000 in regions,
  where `funk` on its 1 GiB stack overflows
  ([#36](https://github.com/pmatos/funk/issues/36)).

## Decision

- **Three targets in `lean/lakefile.lean`, all default targets.** The library
  `Fir` is the spec: the parser and, later, the validation check and the
  interpreter are spec definitions with prose beside them. The library
  `FirRef` and the executable `fir-ref` (root `FirRef.Main`) hold what is
  not the spec: the command line, reading files, bytes that are not UTF-8,
  and output. The library `FirTest` holds the Lean tests. So `lake build` in
  `lean/` builds the spec, `fir-ref` and the tests, and runs the tests. The
  document renders `Fir` only.
- **Unit tests are `#guard` checks in `lean/FirTest/`.** They test spec
  definitions on texts written in Lean, such as each parse error with its
  position, mirroring `crates/funk-ir/tests/`. Characters that the hooks
  keep out of files are written as Lean escapes. A spec chapter may keep a
  few checks of its own, as illustrations.
- **Tests over files run the built `fir-ref`.** `scripts/check-fir-ref.sh`
  has one mode per check:
  - `test`: `fir-ref fmt --check` on every text of `tests/fir/canonical/`,
    and each text of `tests/fir/noncanonical/` printed as its canonical
    sibling.
  - `round-trip`: the cross-language round trip. The Cargo example
    `crates/funk-ir/examples/fir_texts.rs` prints every text of
    `tests/fir/` and the first 600 modules of the Rust generator into a
    temporary directory, and `fir-ref fmt --check` must find each one
    canonical: Lean reprints it with identical bytes.

  Later checks over files, such as `fir-ref validate` and `fir-ref run`
  against the corpus, add modes or texts here or in #13's runner.
- **One guarded build.** `scripts/build-spec.sh --lean` runs `lake build`
  in `lean/` under both guards of ADR-2026-10-29-2135, without the
  document. `fir-ref` is then `lean/.lake/build/bin/fir-ref`. Every script
  and hook that needs `fir-ref` calls this mode; none runs Lake itself.
- **Hooks.** `fir-spec` builds `lean/` and the document, as before; its
  `lake build` now runs the tests too. `fir-ref-test` runs
  `scripts/check-fir-ref.sh test` when `lean/`, `tests/fir/` or the two
  scripts change. `fir-round-trip` runs `scripts/check-fir-ref.sh
  round-trip` when those, the Rust crates or the Rust toolchain change. CI
  needs no new step.
- **`fir-ref`'s command line follows `funk`'s.** `fir-ref COMMAND ...`,
  with the exit status of ADR-2026-10-30-1032: 0 accepted, 1 rejected, 2 a
  usage or I/O error. A parse error is reported as
  `FILE:LINE:COL: parse error: REASON`. The first command is
  `fmt [--check] FILE...`, which prints a text in canonical form with the
  spec's printer, as `funk fmt` does; #13 uses it to check that both sides
  print each non-canonical input as its canonical sibling. `validate` and
  `run` follow, with the JSON output that #10 specifies.
- **No stack of its own.** `fir-ref` runs on the main thread that Lean's
  runtime gives it. When #36 is decided, `fir-ref` follows it: a nesting
  limit in the spec becomes a parse error in the grammar step, and explicit
  stacks replace the recursion of the readers.

## Alternatives

- **`lake test` with a test driver.** It would be a second Lake entry point
  to guard, for what `lake build` already does.
- **Tests at elaboration time with `#eval` and file I/O.** They would depend
  on Lake's working directory, and would not run the `fir-ref` binary.
- **A separate test executable for the shared texts.** #13 needs `fir-ref`
  to print non-canonical inputs anyway, so one binary serves both.
- **A thread with a reserved stack**, as `funk` has. The runtime's main
  thread already parses deeper texts than `funk`; a Lean thread's stack size
  is set through an internal runtime function, not a stable API.

## Consequences

- Building `lean/` builds `fir-ref` and runs every Lean test, so the
  `fir-spec` hook and `scripts/build-spec.sh --lean` fail on a failing test.
- A new parser test is a `#guard` in `lean/FirTest/`; a new shared text is a
  file in `tests/fir/`, and both sides check it with no code change.
- Docstrings in `FirRef` and `FirTest` are Verso markup too, since
  `doc.verso` is a package option.
- `lean/.lake` is not cached in CI, so every CI run builds `lean/` from
  scratch.
- The cross-language round trip covers the ops the Rust registry has. As
  op families land in Rust, the generator and the corpus cover them, and so
  does this check.
