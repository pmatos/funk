# The differential harness is a Python program, `scripts/harness/`, that `scripts/check-harness.sh` runs over the corpus

Status: accepted; extended by ADR-2026-10-31-0003

## Context

[#13](https://github.com/pmatos/funk/issues/13) asks for one runner over
the corpus of `tests/fir/`. It checks that `funk verify` and
`fir-ref validate` give the same verdict on every corpus module, every
module of the Rust generator and every must-reject text. It runs each test
on `fir-ref run` and, for a differential test, as native code from
`funk build`, and judges each test as ADR-2026-10-30-2135 says. The
language and the place are ours to choose: the repository has Rust, Lean,
Python for hooks, and shell. The roadmap's "The toolchain is Rust" names
the IR library, verifier, passes, backends and driver; the harness is a
test tool that judges the toolchain, not part of it.

Facts:

- Every tool reports in JSON: `funk verify --json` and `fir-ref validate`
  (ADR-2026-10-30-1032, ADR-2026-10-30-1741), `fir-ref run`
  (ADR-2026-10-30-1856), and a built executable (ADR-2026-10-30-1233).
- The Rust workspace has no third-party crates, and only a JSON writer
  (ADR-2026-10-30-1030). Python's standard library reads JSON, and TOML
  from Python 3.11 (`tomllib`).
- The Cargo example `fir_texts` already prints the generator's modules to
  files (ADR-2026-10-30-1250).
- The harness judges two implementations against each other, so it should
  share no code with either.

## Decision

- **Python, standard library only.** The harness is the package
  `scripts/harness/`: `main.py` (the command line), `corpus.py` (the
  format of ADR-2026-10-30-2050), `tools.py` (runs the tools and reads what
  they print), `refine.py` (the judgement of ADR-2026-10-30-2135),
  `checks.py` and `report.py`, with unit tests in `test_*.py`. It needs
  Python 3.11 or later.
- **One command.** `scripts/check-harness.sh` builds `fir-ref` with
  `scripts/build-spec.sh --lean`, builds `funk`, has `fir_texts` print the
  corpus's texts and the generator's modules into a temporary directory,
  and runs `main.py --funk FUNK --fir-ref FIR_REF --generated DIR tests/fir`.
- **Verdicts.** Each text goes through `funk verify --json` and
  `fir-ref validate`, one process per text. Corpus and generated modules
  must be accepted by both. A must-reject text must get the verdict its
  file names from both, `parse-error` or `validation-error`; a parse error
  must be at the same line and column, since the text breaks one rule
  (ADR-2026-10-30-1741). Counts and messages are never compared.
- **Tests.** The tests of a module run only when both tools accept it. A
  module with a differential test is built once with `funk build`. Each
  test runs `fir-ref run --fuel N -- FILE @FUNC ARG...`, and a differential
  test also runs the executable with `@FUNC ARG...`. ADR-2026-10-30-2135
  says how each test is judged.
- **What the tools print.** Each tool must print one JSON object on one
  line, as its ADR says, and exit with the status that goes with its
  verdict or result; native code also prints nothing on standard error.
  Anything else fails the check, and the report shows what the tool
  printed.
- **Report.** One line per check on standard output, starting with
  `passed`, `failed` or `invalid`, then the check and both results. Passed
  generated modules are counted, not listed. A last line counts each kind.
  The exit status is 0 when every check passed, 1 when one failed or was
  invalid, and 2 on a usage error or a tool that cannot be started. A
  process that runs for 120 seconds is stopped and fails its check.
- **Hooks.** `fir-harness` runs `scripts/check-harness.sh` at the default
  stage when `lean/`, `crates/`, `tests/fir/`, a Cargo file, the Rust pin or
  one of its scripts changes, so CI runs it on every PR. `fir-harness-test`
  (`language: python`) runs the unit tests when `scripts/harness/` changes.

## Alternatives

- **A Rust crate in the workspace.** It could call `funk-ir`'s generator
  and parser in process, but it needs a JSON reader of its own, its
  sidecars would be JSON with no comments, and it would read the corpus
  with the parser it checks.
- **Shell, like `scripts/check-fir-ref.sh`.** No JSON or TOML reader, and
  judging lists of values by refinement in bash is fragile.
- **One process per tool over all the texts.** Faster, but a crash loses
  the verdicts of the texts after it. One process per text takes a few
  seconds for the whole corpus.

## Consequences

- A new test is a new line or file in `tests/fir/`, with no code change.
- The hook needs elan, rustup and GNU binutils, which the CI job installs.
  A commit that changes `lean/`, `crates/` or `tests/fir/` runs it locally.
- `scripts/check-fir-ref.sh test` keeps its table of `fir-ref run`
  results: it tests `fir-ref`'s command line for #10. New expected results
  go in the corpus's sidecars.
- A corpus text with an op that `funk` does not register yet, or `add` with
  flags, fails the harness. Such texts land with their op family, #14 to
  #20, when both tools have the op.
