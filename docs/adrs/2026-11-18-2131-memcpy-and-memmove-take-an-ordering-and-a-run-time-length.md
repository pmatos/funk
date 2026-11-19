# memcpy and memmove take an ordering and a run-time length in units

Status: accepted
Tier: direction; area: semantics

## Decision

- **Spelling.** `memcpy ORDERING %d, %s, %n` and `memmove ORDERING %d, %s,
  %n`, destination, source and length in C's and LLVM's order, with no
  result. The ordering is always written, and validation in M1 accepts
  `nonatomic` alone, as for loads (ADR-2026-11-14-2316). `memset` takes the
  same form when #234 adds it. In Lean both are `Core.Op.memCopy` with a
  `CopyKind`, `copy` or `move`.
- **One memory.** Both pointers are `ptr<N>` of one memory `N`; pointers
  of two memories do not decode.
- **The length** is a run-time `iW` of any width, read as unsigned, and
  counts units of memory `N`, not bytes.
- **No `align(A)` in M1.** Each access is aligned to one unit, so it is
  never misaligned. An attribute can be added later without changing a
  program written before it.
- **Poison.** A poison pointer is UB when the length is not 0. A poison
  length runs as some length, chosen as `freeze` chooses bits, so it is UB
  wherever some length is (ADR-2026-10-29-2006), and otherwise copies some
  length. The op's poison class is `propagates`. This rule is agent work:
  it replaces the stage plan's "a poison length is UB", which the class
  forbids, and it waits for the human's ruling on #234.

ADR-2026-11-09-1551 gives the meaning of the ops: the zero length and
overlap rulings of 2026-11-18 on #234.
[semantics-m1-design.md](../decisions/semantics-m1-design.md#memory-intrinsics)
states each rule.

## Why

ADR-2026-11-09-1551 has frontends lower C's `memcpy` to the copy op, and a
C call's length is a run-time value, so the length is an operand. The
`mem` names keep the ops apart from Rust's `move` and from the words of the
generic text. The ordering is written for the reason a load's is
(ADR-2026-11-09-1542). Under the propagates class, a poison operand may be
UB only where some defined value in its place is, and monotonicity then
asks a poison length to do what some defined length does.

## Rejected alternatives

- **A poison length is always UB, as in LLVM's LangRef.** With an `i1`
  length over a live allocation of one unit, neither length is UB, so the
  op would be UB on poison where no defined value is, which the
  propagates class forbids. It would need the class `exception`.
- **A length in bytes.** A memory's unit need not be a byte.
- **An immediate length.** C's `memcpy` takes a run-time length.
