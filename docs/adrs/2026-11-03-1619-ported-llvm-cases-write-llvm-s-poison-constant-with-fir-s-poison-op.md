# Ported LLVM cases write LLVM's poison constant with fir's op `poison`

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

ADR-2026-11-03-0644 fixes the rules by which LLVM's test cases are
rewritten into fir. fir had no poison constant, so its rule wrote one as
`%p = shl %n, %n`, with `%n` a `const` of the width, which the spec makes
poison on every run. Eight functions used it: `@poison2` and `@poison3`
in `tests/fir/llvm/instsimplify-select.fir`, and `@poison` to `@poison6`
in `tests/fir/llvm/instsimplify-shift.fir`. The stand-in is two ops that
a reader must know to be poison, and the coverage matrix counts it as a
`const` and a `shl`. ADR-2026-11-03-1615 adds the op `poison`.

## Decision

- LLVM's `poison` constant of type `iN` becomes `%p: iN = poison`, at the
  location of the ops that use it. This replaces ADR-2026-11-03-0644's
  rule for a poison constant; its other rules stand.
- The eight functions above use it. Their tests stay as they are: both
  forms give poison on every run, so each run's outcome is the same.
- The sidecars' comments and `tests/fir/llvm/README.md` say so.

## Consequences

- A ported case that uses LLVM's poison reads as LLVM's does.
- The matrix counts those functions' poison as `poison` at `i32`, and
  no longer as a `const` and a `shl`.
