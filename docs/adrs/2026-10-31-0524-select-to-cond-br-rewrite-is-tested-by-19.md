# The forbidden rewrite of `select` into `and` is tested by #16, and the one into `cond_br` by #19

Status: accepted

## Context

ADR-2026-10-30-0818 states two forbidden rewrites: a `select` becomes a
branch only with its condition frozen, and `select %c, %x, false` is not
`and %c, %x` when `%x` may be poison. It says "#16 tests both". But
[#16](https://github.com/pmatos/funk/issues/16) has no `cond_br`, which
[#19](https://github.com/pmatos/funk/issues/19) adds, so #16 cannot test
the branch. The test moved to #19.

## Decision

This refines ADR-2026-10-30-0818's sentence "#16 tests both":

- #16 tests the `and` rewrite:
  [`select-and`](../../tests/fir/canonical/select-and.toml).
- #19 tests the `cond_br` rewrite:
  [`select-cond-br`](../../tests/fir/canonical/select-cond-br.toml), and
  [`FirTest.Branch`](../../lean/FirTest/Branch.lean) in Lean.

## Consequences

ADR-2026-10-30-0818's decision and body are unchanged, as an accepted
ADR's are; only its status line gains "refined by", as other ADRs'
status lines do. [`PoisonUB.lean`](../../lean/Fir/Execution/PoisonUB.lean)
already names both tickets.
