# Current decisions: generated programs and fuzzing

This page continues [testing-and-harness.md](testing-and-harness.md). It says
what holds today for the programs that a generator writes and for fuzzing. It
is the record: when this page and an ADR disagree, the page wins, and the ADR
is fixed or deleted (ADR-2026-11-09-1610).

## Generated programs

Every pull request runs generated programs on `fir-ref` and as native code
(ADR-2026-11-08-2115). The `fir-random` hook,
`scripts/check-random-programs.sh`, runs seeds 0 to 499, the regression seeds
and 500 random texts for `fir-ref fmt`.

`generate::program` makes a module of the backend's widths and argument vectors,
often at boundary values. Its functions are random, bounded (`bounded.rs`), or
planted to end in UB or out of fuel. Arguments hold no `poison`, since each one
multiplies native runs.

A generated run is judged differently from a corpus test:

- A planted run must end as planted on `fir-ref`. Each kind of UB has a near
  miss, one operand away, whose result the generator states.
- The first bounded function of each program, and half of the others, stay
  defined. A report of UB, poison, a choice or no fuel on their runs fails them.
- Any other run with UB or no fuel in its set is interpreter-only and passes.
  So is one that chooses past 10 bits. `differential.evaluate_generated`
  judges it.
- Otherwise the run is a differential test by the corpus's rules.
- A stuck path fails in every case.

Ordinary runs have 20,000 steps of fuel. Runs of the functions that stay
defined have 1,000,000, and planted fuel runs have 1,000 (ADR-2026-11-08-2115).
The hook also guards against an empty check. In
a run of 200 or more, at least half of the runs without an expected ending must
reach native code.

Rejected: limiting the generator to the backend's widths alone. A planted wrong
`ashr` at `i16` passed 500 such programs, since most values never reached a
`ret` (ADR-2026-11-08-2115).

A false UB in a purely random function goes unnoticed. A second interpreter would
cover it, and that is a direction call. A change to the generator changes which
program each seed means. Bounded recursion is at most 15 deep per function. A
random function that returns very deep could outgrow the native stack, which is
that limit, not a miscompile.

### Fresh seeds

Pull requests run fixed seeds, so that a local pass predicts a CI pass. Only a
nightly workflow draws fresh ones. The human ruled this on 2026-11-08, in #165
(ADR-2026-11-08-2116, ADR-2026-11-05-1408).
`fir-random-nightly` and `fir-fuzz` are hooks of the `manual` stage, and
`.github/workflows/nightly.yml` runs them.

A failure prints the seeds to replay and fails the workflow. Nothing files an
issue. Each failure's seed joins `scripts/harness/regression_seeds.txt`, which
every pull request runs. A seed names a program only for the generator of its
day, so the failing program also joins `tests/fir/` as a test.

Rejected: a fresh seed on each pull request, whose failure could land on an
unrelated pull request (ADR-2026-11-08-2116).

## Fuzzing

`fuzz/` is a crate outside the workspace with the targets `parse` and `verify`,
since `cargo-fuzz` needs a nightly compiler and the workspace pins a stable one.
Their checks are in `funk_ir::fuzz`, which the property tests also call. The
`fir-fuzz` hook, `scripts/check-fuzz.sh`, runs each target for 10 minutes on the
pinned nightly compiler, with no sanitizer. `funk-ir` forbids unsafe code, so a
sanitizer has little to find, and a panic ends the run without one. There is no
Lean fuzzer: the human ruled that on 2026-11-08 (#165).

Rejected: Address Sanitizer, which ran about one input per 3 seconds, where
the run without it took 2 million in 11 seconds. Memory errors in a
dependency's unsafe code go unnoticed.

Every input the fuzzers keep goes through `fir-ref fmt`, as do the random texts.
It must print a canonical form or report a parse error at a position. An exit
status alone does not count, since an uncaught exception also exits with 1.
`scripts/harness/fuzz_to_corpus.py` keeps a crash once the bug is fixed: a
rejected text in `tests/fir/reject/fuzz.toml`, a valid module in
`tests/fir/canonical/`.

### Fuzzing the round trip

The round trip is also fuzzed over well-formed modules, a larger set than valid
ones (ADR-2026-10-29-2014). The human decided this in triage on 2026-11-05
(#146): in Rust and across languages, with `fir-ref fmt` reprinting each text
without `fir-ref validate` accepting it first.

`generate::wellformed::module` makes them from a valid module of
`generate::module`. `Dialects::Core` puts regions on core ops, and
`Dialects::CoreAndToy` adds the test op `toy.any`, the only op with string and
applied attributes. `crates/funk-ir/tests/wellformed.rs` checks both directions
on the first 600 modules of each kind, and that each shape of #146 is in at
least a tenth of them. `fir-ref fmt --check` must reprint the first 600
core-dialect modules byte for byte, and nothing validates them. `fir-ref`
cannot read string attributes, applied attributes or other dialects, so only
Rust fuzzes those, and Lean proves the round trip for every lawful dialect
(`printThenParse`).
