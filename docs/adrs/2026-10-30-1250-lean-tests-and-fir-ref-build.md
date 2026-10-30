# fir's Lean code is tested by `#guard` checks and by `fir-ref` over the shared texts, and `fir-ref` is built by `build-spec.sh --lean`

Status: accepted

## Context

ADR-2026-10-29-2135 makes `lean/` the Lake package `fir`, with no
dependencies, built by `scripts/build-spec.sh` under two git guards. It
leaves to [#10](https://github.com/pmatos/funk/issues/10) how the Lean code
is tested and how the `fir-ref` executable is built. ADR-2026-10-30-1425
gives `fir-ref`'s command line.

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
- fir has no nesting limit. The human ruled so on
  [#36](https://github.com/pmatos/funk/issues/36) on 2026-10-30: every
  tool, `fir-ref` included, must give a verdict on a text nested to any
  depth, without a stack overflow.

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
    each text of `tests/fir/noncanonical/` printed as its canonical
    sibling, and a text with a string of ten million characters reprinted
    on a 256 KiB stack.
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
- **No reserved stack.** `fir-ref` runs on the main thread that Lean's
  runtime gives it. Since fir has no nesting limit, depth must not cost
  stack: [#47](https://github.com/pmatos/funk/issues/47), the next stage of
  #10, gives `fir-ref` implementations of the spec's readers, decoder and
  printer that take no stack per level, and its own ADR records how.

## Alternatives

- **`lake test` with a test driver.** It would be a second Lake entry point
  to guard, for what `lake build` already does.
- **Tests at elaboration time with `#eval` and file I/O.** They would depend
  on Lake's working directory, and would not run the `fir-ref` binary.
- **A separate test executable for the shared texts.** #13 needs `fir-ref`
  to print non-canonical inputs anyway, so one binary serves both.
- **A thread with a reserved stack, or a stack sized from the input.**
  Either moves the depth at which `fir-ref` aborts instead of removing it,
  which the ruling on #36 does not allow. A Lean thread's stack size is also
  set through an internal runtime function, not a stable API.

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
- `fir-ref` decodes every core op, while `funk` registers only `const`,
  `add` without flags and `ret` until #14 to #20 land. Until then a text
  with another op, or with flags on `add`, parses in `fir-ref` and is a
  parse error in `funk`, so #13 compares their verdicts only on texts that
  use `funk`'s ops.
- `fir-round-trip` needs both toolchains. A commit that changes `crates/`,
  `Cargo.toml`, `Cargo.lock` or `rust-toolchain.toml` builds `lean/`, so it
  needs elan; one that changes `lean/` needs rustup. ADR-2026-10-29-2135
  says that work which touches no Lean file is not blocked without elan;
  that no longer holds for the Rust crates.
- Until #47 lands, the spec's readers, decoder and printer recurse once per
  level of nesting on the main thread. Measured on 2026-10-30, `fir-ref`
  aborts with a stack overflow on attributes nested 7,000,000 levels deep,
  and on regions and items nested 3,000,000 and 10,000,000 deep. Strings
  take no stack: `check-fir-ref.sh test` reprints one of ten million
  characters on a 256 KiB stack.
