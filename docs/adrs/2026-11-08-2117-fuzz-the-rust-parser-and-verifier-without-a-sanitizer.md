# The Rust parser and verifier are fuzzed without a sanitizer

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

#165 asks for coverage-guided fuzzing of the Rust parser and verifier, and a
way to keep what it finds. `cargo-fuzz` needs a nightly compiler, and the
workspace pins a stable one. `cargo-fuzz` reaches only Rust, and the human
ruled on 2026-11-08 that there is no Lean fuzzer.

With Address Sanitizer, a target ran about one input per 3 seconds here.
Without it, it ran 2 million in 11 seconds.

## Decision

- `fuzz/` is a crate outside the workspace with the targets `parse` and
  `verify`. Their checks are in `funk_ir::fuzz`, which the property tests
  also call, so stable builds compile and run them.
- `scripts/check-fuzz.sh`, the `fir-fuzz` hook, runs each target for 10
  minutes on the pinned `nightly-2026-10-01`, with `--sanitizer none`.
  `funk-ir` forbids unsafe code, so a sanitizer has little to find, and a
  panic ends the run without one.
- Every input that the fuzzers keep goes through `fir-ref fmt`, as do the
  random texts of the `fir_programs` example. It must print a canonical
  form or report a parse error at a position. An exit status alone does not
  count, since an uncaught exception also exits with 1.
- `scripts/harness/fuzz_to_corpus.py` keeps a crash once the bug is fixed: a
  rejected text in `tests/fir/reject/fuzz.toml`, a valid module in
  `tests/fir/canonical/`.

## Consequences

- Memory errors in a dependency's unsafe code would go unnoticed.
- Malformed texts reach the Lean parser, but only those that the Rust
  fuzzers keep and the random texts: nothing guides a search through Lean.
