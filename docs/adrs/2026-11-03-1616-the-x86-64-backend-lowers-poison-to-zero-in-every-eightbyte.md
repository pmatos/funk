# The x86-64 backend lowers `poison` to zero in every eightbyte

Status: accepted
Tier: implementation; area: x86-64-backend

## Context

ADR-2026-11-03-1615 adds `poison`, a constant op whose result is poison.
Native code holds no poison: every value is the bits in its slot
(ADR-2026-10-30-2248), and any value refines poison (S4,
ADR-2026-10-29-2008). The human ruled that native code may lower `poison`
to any value (#122). Every value has a slot of its own
(ADR-2026-10-30-1230); an `iN` lives in the low `N` bits of an eightbyte
(ADR-2026-10-30-1231), and an `i128` in two (ADR-2026-11-03-010730).

## Decision

- `poison` writes zero into each eightbyte of its result's slot, with
  `movq $0`: one at `i1` to `i64`, two at `i128`
  (`crates/funk-x86-64/src/lower/constant.rs`).
- **Why a fixed value.** A `poison` that wrote nothing would leave the
  bits that the slot held before, so a native run that returns the
  poison, or freezes it, would give what the frame happened to hold, and
  could differ from run to run and build to build. Native runs are
  checked against `fir-ref`; a failure must reproduce.
- **Why zero.** It is a value of every width with no masking: `false` at
  `i1`, and two zero halves at `i128`. It costs one instruction per
  eightbyte.

This does not reopen ADR-2026-10-30-2248's rejection of a fixed value for
frozen poison: that would need code to know at run time whether a value
is poison. `freeze` still copies its operand. `poison` is poison where it
is written, so the backend knows it at compile time.

## Alternatives

- **Write nothing.** No code, but native results that depend on chance.
- **A recognisable pattern**, such as alternating bits, to make poison
  visible in a debugger. At `i1` it would need masking to be a value,
  and no test can tell it from zero.

## Consequences

- A native run cannot tell `poison` from `const 0`, so the coverage
  matrix counts its differential tests by what they run
  (ADR-2026-11-03-1618).
- An optimizer (M1) may lower `poison` to anything, or fold it away,
  under the same rule.
