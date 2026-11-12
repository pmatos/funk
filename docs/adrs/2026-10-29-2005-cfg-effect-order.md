# fir is a CFG, and effectful ops are ordered by their position in a block

Status: accepted
Tier: direction; area: semantics

## Decision

- fir is a CFG: a function body is a graph of blocks, linked by branches. It
  is not a sea of nodes and not an RVSDG.
- Effectful ops are ordered by their position in a block. An earlier op's
  effects happen before a later op's. A pass that moves an effectful op must
  keep every effect order the source fixes.
- This order binds the core dialect. Extension dialects may define other
  region kinds, such as unordered dataflow regions (G0,
  ADR-2026-10-29-2016), as ADR-2026-11-09-1543 admits.
- Explicit memory tokens may come later as a stricter mode, without
  replacing the CFG.

This is E0 of the fir v0 decision record, agreed on 2026-10-29 (#5).
[semantics.md](../decisions/semantics.md) states what holds.

## Why

The Lean interpreter, the text format and the backend all need a definite
order for effectful ops. In a CFG the interpreter runs a block's ops in
order, the printer prints them in order and a naive backend emits them in
order, as in LLVM and Cranelift.

## Rejected alternatives

- **Sea of nodes.** Ops float free, ordered only by dependence edges.
  Printing, interpreting or lowering a function then needs a scheduling step
  to recover an order.
- **RVSDG.** Regions with explicit state edges for effects. Same cost: the
  order is implicit in edges, not visible in a block.
