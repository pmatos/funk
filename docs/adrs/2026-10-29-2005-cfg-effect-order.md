# fir is a CFG, and effectful ops are ordered by their position in a block

Status: accepted

## Context

This is decision E0 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

An IR must say in what order effects happen. A control-flow graph (CFG) keeps
an ordered list of ops in each block, as LLVM and Cranelift do. Graph forms
such as a sea of nodes or an RVSDG keep no list: order comes only from explicit
dependence edges. The Lean interpreter, the text format and the naive backend
of M0 all need a definite order for effectful ops.

## Decision

- fir is a CFG: a function body is a graph of blocks, linked by branches.
- Effectful ops are ordered by their position in a block. An earlier op's
  effects happen before a later op's.
- fir is not a sea of nodes and not an RVSDG.
- Explicit memory tokens may come later as a stricter mode. This ADR does not
  add them; the memory model (S3) is still open.
- E0 binds the core dialect. Extension dialects may later define other region
  kinds, such as unordered dataflow regions (G0, ADR-2026-10-29-2016).

## Alternatives

- **Sea of nodes.** Ops float free, ordered only by dependence edges. Printing,
  interpreting or lowering a function then needs a scheduling step to recover
  an order.
- **RVSDG.** Regions with explicit state edges for effects. Same cost: the order
  is implicit in edges, not visible in a block.

## Consequences

- The reference interpreter runs a block's ops in order, the printer prints
  them in order, and the naive backend emits them in order.
- A pass that moves an effectful op must show that the move keeps every effect
  order the source fixes.
- Stricter ordering, through memory tokens, can be added later as a mode
  without replacing the CFG.
