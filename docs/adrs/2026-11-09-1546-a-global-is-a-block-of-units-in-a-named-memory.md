# A global is a symbol for a block of units in a named memory, with a constant initializer and a linkage

Status: accepted
Tier: direction; area: semantics

## Decision

- **A global item** has a symbol; the memory it lives in, the default memory
  when none is given; a size in that memory's units and an alignment; an
  initializer of constant units, which may include the address of a symbol
  plus an offset (`@f`, `@g + 8`), so tables of pointers and vtables can be
  built; a `const` flag, where writing a constant global is UB; and a linkage,
  `internal` (the default) or `export`.
- **Its allocation.** Each global is one allocation of kind global, live for
  the whole run. An op gets its address by symbol. A frontend writes initial
  data as units and relocations, as an assembler does.
- **Linkage.** An `export` global is visible to code that funk did not
  compile and is observed at the end of a run. An `internal` global is
  observed only once its address escapes (ADR-2026-11-09-1540). Weak, common
  and visibility linkage wait for the C frontend (M4).

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #209.

## Why

H3 (ADR-2026-10-29-2012) has ops refer to functions and other globals by
symbol only, and M0 has no global data. Memory is logical blocks in typed
memories (ADR-2026-11-09-1542), so a global is one such block, and a global
in a GPU memory is written by naming that memory. A C frontend lays out bytes
and relocations anyway.

## Rejected alternatives

- **Typed globals,** holding a fir value such as an integer or an aggregate.
  That would tie globals to the shape of aggregates (ADR-2026-11-09-1550).
- **Every global exported, with no linkage.** Wrong for C's `static`, whose
  stores could then never be removed.
