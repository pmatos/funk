# A global is a symbol for a block of units in a named memory, with a constant initializer and a linkage

Status: accepted

## Context

H3 (ADR-2026-10-29-2012) says ops refer to functions and other globals by
symbol only, but M0 has no global data. Under ADR-2026-11-09-1543 a global
is a kind of item. Memory is logical blocks in typed memories
(ADR-2026-11-09-1542). The human ruled on
[#209](https://github.com/pmatos/funk/issues/209) on 2026-11-09.

## Decision

- **A global item** has:
  - a symbol;
  - the memory it lives in, the default memory when none is given;
  - a size in that memory's units, and an alignment;
  - an initializer of constant units, which may include the address of a
    symbol plus an offset (`@f`, `@g + 8`), so tables of pointers and
    vtables can be built;
  - a `const` flag: writing a constant global is UB;
  - a linkage, `internal` (the default) or `export`.
- **Its allocation.** Each global is one allocation of kind global, live
  for the whole run. An op gets its address by symbol.
- **Linkage.** An `export` global is visible to code that funk did not
  compile and is reachable memory for an observer (ADR-2026-11-09-1540).
  Weak, common and visibility linkage wait for the C frontend (M4).

## Alternatives

- **Typed globals,** holding a fir value such as an integer or an
  aggregate. That would tie globals to the shape of aggregates
  (ADR-2026-11-09-1550), and a C frontend lays out bytes anyway.
- **Every global exported, with no linkage.** Wrong for C's `static`.

## Consequences

- A frontend writes initial data as units and relocations, as an assembler
  does.
- A global in a GPU memory is written by naming that memory.
