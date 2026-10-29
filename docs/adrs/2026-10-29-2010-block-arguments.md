# fir is SSA with block arguments, not phis

Status: accepted

## Context

This is decision H1 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

In SSA form, a value that differs by the path taken into a block must be
merged at the block's entry. LLVM does this with phi nodes, which must sit at
the start of a block and list one incoming value per predecessor. MLIR,
Cranelift and Swift SIL instead give blocks arguments, which every branch to
the block passes.

## Decision

- fir is in SSA form, with block arguments and no phis.
- A block declares typed arguments, for example `loop(%i: i32, %acc: i32):`.
- A branch passes one value per argument of its target, for example
  `br loop(%i1, %acc1)`. `br` and `cond_br` both pass block arguments.

The examples follow the epic's sketch. The concrete syntax is the spec's
([#8](https://github.com/pmatos/funk/issues/8)).

## Alternatives

- **Phi nodes** (LLVM). Rejected: block arguments make a branch a jump that
  carries values, like a call, and need no rule tying phis to predecessors.

## Consequences

- The verifier checks, at every branch, that the values passed match the
  target's argument count and types.
- The interpreter binds a block's arguments when it jumps there, and needs no
  memory of which edge it came from.
- The backend must move each passed value into its block argument on every
  edge into the block.
