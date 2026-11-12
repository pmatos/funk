# Native code holds no poison: flagged ops wrap, and freeze copies its operand

Status: accepted
Tier: direction; area: x86-64-backend

## Decision

- **No poison at run time.** Native code has no poison value: every value is
  the bits in its slot. An op whose result in the source is poison still
  stores some bits there, and nothing relies on which.
- **Flags cost nothing.** `add`, `sub` and `mul` lower the same with any flags
  as without. Where a flag is broken, the result is the wrapped one, which
  refines poison. No code tests a flag.
- **`freeze` is a copy.** It loads its operand and stores the bits as its own
  value, which no other op writes, and every use reads that, so every use sees
  the same bits. A `freeze` that runs twice, as in a loop, may give other bits
  each time.
- **What an optimizer keeps.** A later optimizer that makes poison real at
  compile time, from a flag or from any op whose rule gives poison, must keep
  each `freeze` one value that every use reads. It may not fold a `freeze`
  away, or copy it into each use, where its operand may be poison. Both halves
  of a frozen `i128` stay one value.

How each op lowers, and the op `poison`'s fixed zero, are on
[x86-64-backend.md](../decisions/x86-64-backend.md#poison).

## Why

Native code is correct when it refines the source, and any value refines
poison (ADR-2026-10-29-2008). `freeze` of poison gives an arbitrary value, and
every use of its result sees the same bits (ADR-2026-10-29-2017). Native code
cannot know whether a value is poison without tracking it, and no one reads
such tracking.

## Rejected alternatives

- **Trap on a broken flag.** That makes poison immediate UB. Poison that is
  frozen or never used must not stop the program.
- **A fixed value, such as zero, for frozen poison.** Code would have to know
  at run time whether a value is poison.
- **A poison bit per value**, or per half of an `i128`. Nothing reads it, since
  any value refines poison.
