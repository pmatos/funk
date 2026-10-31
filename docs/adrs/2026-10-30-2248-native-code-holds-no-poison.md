# Native code holds no poison: flagged ops wrap, and freeze copies its operand

Status: accepted

## Context

[#14](https://github.com/pmatos/funk/issues/14) brings the flags `nuw` and
`nsw` of `add`, `sub` and `mul`, and `freeze`, to the x86-64 backend. A
broken flag gives poison (S1, ADR-2026-10-29-2006). `freeze` of poison gives
an arbitrary value, and every use of its result sees the same bits
(ADR-2026-10-29-2017). Native code is correct when it refines the source,
and any value refines poison (S4, ADR-2026-10-29-2008). The backend gives
every value a slot of its own (ADR-2026-10-30-1230) and holds `iN` in the
low `N` bits of 64 (ADR-2026-10-30-1231).

## Decision

- **No poison at run time.** Native code has no poison value: every value
  is the bits in its slot. An op whose result in the source is poison
  still stores some bits there, and nothing relies on which.
- **Flags cost nothing.** `add`, `sub` and `mul` lower the same with any
  flags as without: one `addq`, `subq` or `imulq`. Where a flag is broken,
  the result is the wrapped one, which refines poison. No code tests a
  flag.
- **`freeze` is a copy.** It loads its operand's slot and stores the bits
  in its own. Only the `freeze` writes that slot, and every use of its
  result loads it, so every use sees the same bits. Each time the op runs
  it copies again, so a `freeze` that runs twice, as in a loop, may give
  other bits each time, as the spec allows.

## Alternatives

- **Trap on a broken flag.** That makes poison immediate UB. Poison that is
  frozen or never used must not stop the program.
- **A fixed value, such as zero, for frozen poison.** Code would have to
  know at run time whether a value is poison, which native code cannot
  know without tracking it, and the spec allows any value.

## Consequences

- Tests of a broken flag accept any value of the type, and tests of
  `freeze` check that its uses agree, as `sub %f, %f` giving `0` does.
- A later optimizer (M1) that exploits poison makes poison real at compile
  time, whether it comes from a flag, as LLVM does, or from any op whose
  rule gives poison, such as a shift by `N` or more
  ([#15](https://github.com/pmatos/funk/issues/15)). It must then keep
  each `freeze` one value that every use reads: it may not fold a `freeze`
  away, or copy it into each use, where its operand may be poison.
