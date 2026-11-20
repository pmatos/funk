# memcpy, memmove and memset take an ordering and a run-time length in units

Status: accepted
Tier: direction; area: semantics

## Decision

- **Spelling.** `memcpy ORDERING %d, %s, %n` and `memmove ORDERING %d, %s,
  %n`, destination, source and length in C's and LLVM's order, with no
  result. The ordering is always written, and validation in M1 accepts
  `nonatomic` alone, as for loads (ADR-2026-11-14-2316). `memset ORDERING
  %d, %v, %n` takes the same form, with the value in the source's place. In
  Lean the first two are `Core.Op.memCopy` with a `CopyKind`, `copy` or
  `move`, and the third is `Core.Op.memSet`.
- **The fill's value** is an `iV` as wide as a unit of memory `N` (the
  human's ruling on #251). The module's data-layout rule checks it, as it
  checks the memories that types name: each op lists the pairs of a memory
  and a width it asks (`opUnits`), and the layout's entry must agree.
- **One memory.** The pointers of `memcpy` and `memmove` are `ptr<N>` of
  one memory `N`; pointers of two memories do not decode.
- **The length** is a run-time `iW` of any width, read as unsigned, and
  counts units of memory `N`, not bytes.
- **No `align(A)` in M1.** Each access is aligned to one unit, so it is
  never misaligned. An attribute can be added later without changing a
  program written before it.
- **Poison.** A poison pointer is UB when the length is not 0. A poison
  length runs as some length, chosen as `freeze` chooses bits, so it is UB
  wherever some length is (ADR-2026-10-29-2006), and otherwise copies or
  fills some length. The ops' poison class is `propagates`. The human
  ruled this on 2026-11-19 on #234 (option A); a lowering to LLVM freezes
  the length first. A poison value of `memset` writes poison units, as a
  store of poison does.

ADR-2026-11-09-1551 gives the meaning of the ops: the zero length and
overlap rulings of 2026-11-18 on #234.
[semantics-m1-design.md](../decisions/semantics-m1-design.md#memory-intrinsics)
states each rule.

## Why

ADR-2026-11-09-1551 has frontends lower C's `memcpy` to the copy op, and a
C call's length is a run-time value, so the length is an operand. The
`mem` names keep the ops apart from Rust's `move` and from the words of the
generic text. The fill's width is checked at the layout, which already
knows each memory's unit. The ordering is written for the reason a load's is
(ADR-2026-11-09-1542). Under the propagates class, a poison operand may be
UB only where some defined value in its place is, and monotonicity then
asks a poison length to do what some defined length does.

## Rejected alternatives

- **A poison length is always UB, as in LLVM's LangRef.** With an `i1`
  length over a live allocation of one unit, neither length is UB, so the
  op would be UB on poison where no defined value is, which the
  propagates class forbids. It would need the class `exception`.
- **A length in bytes.** A memory's unit need not be a byte.
- **The fill's width checked in the op's own rule.** An op's context has no
  data layout, so every dialect's op rule would gain one.
- **An immediate length.** C's `memcpy` takes a run-time length.
