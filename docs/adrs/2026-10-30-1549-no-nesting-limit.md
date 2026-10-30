# fir has no nesting limit

Status: accepted

## Context

Attributes (`h(h(x))`), regions (an op's region holds blocks of ops that
own regions) and items (a body of items) nest in fir text and IR. The spec
limits numbers (N3), but not nesting.

`funk-ir` (#9) handled nesting recursively. On its 1 GiB reserved stack,
`funk` gave a verdict on a text nested a million levels deep, but one
nested 3 million levels deep aborted it with a stack overflow and no
verdict, which breaks ADR-2026-10-30-1032. A library caller on a 2 to 8 MB
thread failed after a few thousand levels. The spec's Lean parser and
printer (#10) recurse the same way. #36 asked for a direction call: a
nesting limit, or none.

## Decision

The human ruled on 2026-10-30 (#36): fir has no nesting limit. "There's no
point in introducing a random nesting limit."

- Every text the grammar accepts is read at any depth, and the IR holds
  any depth. The spec has no depth rule.
- Every tool, in Rust and in Lean (`funk-ir`, `funk`, `fir-ref`), handles
  any depth without a stack overflow, on a small stack too. Memory bounds
  how deep a text can go, not the stack. No tool relies on a large
  reserved stack.

## Alternatives

- **A nesting limit in the spec**, like N3: texts nested deeper than N
  levels of `(` and `{` become parse errors, in Rust and Lean alike. It
  changes the text format, which the ruling rejects.
- **A limit in the implementation, reported as a resource error**: `funk`
  and `fir-ref` would disagree on deep texts.

## Consequences

- A walk over nested text or IR keeps its path on the heap, or does
  something equivalent, which takes more code than recursion.
  ADR-2026-10-30-1333 records how `funk-ir` does it.
- `fir-ref` and the spec's Lean parser and printer follow the same rule;
  #47 tracks them.
- The tests of each tool nest texts deeper than a recursive walk on a small
  stack could reach.
