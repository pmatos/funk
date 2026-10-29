# Deferred UB is one poison value with `freeze`, and fir has no `undef`

Status: accepted

## Context

This is decision S1 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

Some failures, such as a signed overflow on an add that promised none, should
not make the op itself undefined, so that the op can still be moved or
speculated. Their result is a deferred-UB value instead: undefined only if it
is used in certain ways. LLVM has two such values, `undef` and `poison`. Each
use of `undef` may see a different value, which makes common rewrites unsound:
`mul %x, 2` is even, but `add %x, %x` can be odd when `%x` is `undef`.

## Decision

- fir has one deferred-UB value, **poison**, plus the `freeze` op. There is no
  `undef`.
- The flags `nsw`, `nuw` and `exact` turn their failure into poison.
- Branching on poison is immediate UB. Division by zero is immediate UB.
- `freeze` of poison yields an arbitrary but fixed value: every use of the
  result sees the same value.

The M0 op set in the epic applies the same split: `INT_MIN / -1` is also UB,
and a shift amount `>= N` gives poison. The spec states the poison and UB rules
of each op.

## Alternatives

- **`undef` as well as poison** (LLVM). Rejected: uses of one `undef` may
  disagree, which breaks rewrites such as the one above.

## Consequences

- Lean, the Rust verifier and the harness model one deferred-UB value, kept
  distinct from immediate UB.
- `freeze` makes a function's behaviour a set of outcomes, not one outcome.
  ADR-2026-10-29-2017 says how the reference interpreter and the differential
  harness handle that set.
- Native code must give every use of one frozen value the same bits.
