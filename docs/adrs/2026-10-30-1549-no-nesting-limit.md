# fir has no nesting limit

Status: accepted
Tier: direction; area: semantics

## Decision

- Every text the grammar accepts is read at any depth, and the IR holds any
  depth. The spec has no depth rule.
- Every tool, in Rust and in Lean (`funk-ir`, `funk`, `fir-ref`), handles any
  depth without a stack overflow, on a small stack too. Memory bounds how
  deep a text can go, not the stack. No tool relies on a large reserved
  stack.
- The tests of each tool nest texts deeper than a recursive walk on a small
  stack could reach.

The human ruled this on 2026-10-30 (#36): "There's no point in introducing a
random nesting limit." [semantics.md](../decisions/semantics.md) states what
holds, and [rust-ir-and-tools.md](../decisions/rust-ir-and-tools.md#nesting)
how `funk-ir` keeps its walks off the stack.

## Why

Attributes, regions and items nest in fir text and IR. A recursive walk
overflowed: `funk` on its 1 GiB reserved stack aborted with no verdict on a
text nested 3 million levels deep, which breaks the one verdict per file of
[rust-ir-and-tools-funk.md](../decisions/rust-ir-and-tools-funk.md#commands-and-verdicts),
and a library caller on a 2 to 8 MB thread failed after a few thousand
levels.

## Rejected alternatives

- **A nesting limit in the spec,** like N3: texts nested deeper than N
  levels become parse errors, in Rust and Lean alike. It changes the text
  format, which the ruling rejects.
- **A limit in the implementation, reported as a resource error.** `funk`
  and `fir-ref` would disagree on deep texts.
