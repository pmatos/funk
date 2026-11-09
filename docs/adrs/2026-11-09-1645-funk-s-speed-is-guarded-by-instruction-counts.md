# funk's speed is guarded by instruction counts against a committed baseline

Status: accepted
Tier: direction; area: rust-ir-and-tools

## Context

The M0 close-out audit found the Rust tools linear but slow, and CI had no
check on their speed. M1 grows the IR, and M2 adds the expensive passes. The
human's ruling on #174 asks for a regression guard now and no speed work: a CI
check that counts instructions, so that it holds under any load, and fails
when a PR is more than about 10% above a baseline recorded on `main`, with
M0's numbers as the start.

## Decision

The `rust-speed` hook runs [`check-rust-speed.sh`](../../scripts/check-rust-speed.sh).
It builds the release `funk` and generates two inputs into a temporary
directory, so that no large input is committed:

- `adds`: one function of 100,000 `add`s at `i32`, each using the one before.
- `blocks`: one function of 20,000 blocks, each passing an `i32` to the next
  with `br`.

It runs `funk fmt --check`, `funk verify` and `funk build` on each one under
`valgrind --tool=cachegrind --cache-sim=no` and reads `I refs`. Children are
not traced, so `as` and `ld` are not counted. A command that exits nonzero
fails the hook, since a command that stops early counts too few instructions.

[`rust-speed-baseline.json`](../../scripts/rust-speed-baseline.json) holds one
count per input and command, the sizes, and the glibc and valgrind they were
measured with. A count fails when `new * 100 > old * 110`. The hook takes the
sizes from the baseline, so changing a size means re-measuring every count.

**CI is the authority.** The baseline comes from CI on `ubuntu-26.04`, and only
a run with `GITHUB_ACTIONS` set can fail. Elsewhere the hook prints the same
table and passes. Counts depend on the host's glibc and valgrind: this Arch
host (glibc 2.44, valgrind 3.25.1) counts 1.75% to 2.28% below `ubuntu-26.04`
(glibc 2.43, valgrind 3.26.0) on the six pairs. No bound on that gap holds for
every host, and a hook that fails on a developer's machine for its libc would
be wrong. So for this hook a local pass does not predict a CI pass, as other
hooks' do: a local run shows the table that CI will judge, and says when a
count is over the margin.

Counts vary a little between runs of one binary, because `HashMap`'s
`RandomState` is seeded per process and is on the measured paths
(`funk-ir/src/ir/module.rs:192`, `verify/func.rs:81` and `:146`,
`text/decode.rs:79`, `funk-x86-64/src/frame.rs:55`). Five runs here varied by
at most 0.73% on `build` of `adds` and under 0.1% elsewhere: small against the
margin.

A PR may raise the baseline only by saying so, with the old and new numbers in
its body, as the Lean side does for its soft limits. A hook cannot read a PR
body, so this is a rule for authors and reviewers, and the JSON diff shows both
numbers. The numbers to commit are the `measured` column of CI's table.

Absolute per-op targets are decided at the start of M2. The Lean side's "up to
10x the Rust side" rule is measured against this baseline.

## Alternatives

- Wall time, or a CPU-time limit like the Lean side's: both move with the host
  and its load, and the ruling asks for a deterministic count.
- Fail on every host: a host-independent limit cannot exist, by the gap above.
- A wider local margin: it is a second limit nobody ruled on, and it still
  assumes a bound on hosts.

## Consequences

A regression over 10% cannot reach `main` unnoticed, and the check takes about
half a minute in CI. It catches no slowdown under 10%, and small ones can add
up until a PR crosses the margin. A runner image's new glibc or valgrind can
move every count at once; that shows in the table, and a PR raises the baseline
as above.
