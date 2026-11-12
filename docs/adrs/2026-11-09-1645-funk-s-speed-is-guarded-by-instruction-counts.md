# funk's speed is guarded by instruction counts against a committed baseline

Status: accepted
Tier: direction; area: rust-ir-and-tools

## Decision

The `rust-speed` hook runs [`check-rust-speed.sh`](../../scripts/check-rust-speed.sh).
It builds the release `funk` and generates two inputs into a temporary
directory, so that no large input is committed:

- `adds`: one function of 100,000 `add`s at `i32`, each using the one before.
- `blocks`: one function of 20,000 blocks, each passing an `i32` to the next
  with `br`.

It runs `funk fmt --check`, `funk verify` and `funk build` on each under
`valgrind --tool=cachegrind --cache-sim=no` and reads `I refs`. Children are
not traced, so `as` and `ld` are not counted. A command that exits nonzero
fails the hook, since a command that stops early counts too few instructions.

[`rust-speed-baseline.json`](../../scripts/rust-speed-baseline.json) holds one
count per input and command, the sizes, and the glibc and valgrind they were
measured with. A count fails when `new * 100 > old * 110`. The hook takes the
sizes from the baseline, so changing a size means re-measuring every count.

**CI is the authority.** The baseline comes from CI on `ubuntu-26.04`, and only
a run with `GITHUB_ACTIONS` set can fail. Elsewhere the hook prints the same
table and passes, so for this hook a local pass does not predict a CI pass.

A PR may raise the baseline only by saying so, with the old and new numbers in
its body. A hook cannot read a PR body, so this is a rule for authors and
reviewers; the JSON diff shows both numbers. The numbers to commit are the
`measured` column of CI's table.

Absolute per-op targets are decided at the start of M2. The Lean side's "up to
10x the Rust side" rule is measured against this baseline.

## Why

The human ruled on 2026-11-09 (#174): a regression guard now and no speed
work, a check that counts instructions so that it holds under any load, a
failure more than about 10% above a baseline recorded on `main`, and a
baseline raised only by saying so with the old and new numbers.

Counts depend on the host's glibc and valgrind: one Arch host counted 1.75%
to 2.28% below `ubuntu-26.04`. No bound on that gap holds for every host.
Counts also vary a little between runs, since `HashMap`'s `RandomState` is
seeded per process: at most 0.73%, small against the margin.

## Rejected alternatives

- Wall time, or a CPU-time limit like the Lean side's: both move with the host
  and its load, and the ruling asks for a deterministic count.
- Fail on every host: a host-independent limit cannot exist, by the gap above.
- A wider local margin: it is a second limit nobody ruled on, and it still
  assumes a bound on hosts.
