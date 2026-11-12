# fir is SSA with block arguments, not phis

Status: accepted
Tier: direction; area: semantics

## Decision

- fir is in SSA form, with block arguments and no phis.
- A block declares typed arguments, for example `loop(%i: i32, %acc: i32):`.
- A branch passes one value per argument of its target, for example
  `br loop(%i1, %acc1)`. `br` and `cond_br` both pass block arguments.
- The verifier checks, at every branch, that the values passed match the
  target's argument count and types.

This is H1 of the fir v0 decision record, agreed on 2026-10-29 (#5).
[semantics.md](../decisions/semantics.md) states what holds.

## Why

A value that differs by the path taken into a block must be merged at the
block's entry. With block arguments, as in MLIR, Cranelift and Swift SIL, the
interpreter binds a block's arguments when it jumps there and needs no memory
of which edge it came from. The backend moves each passed value into its
block argument on every edge into the block.

## Rejected alternatives

- **Phi nodes,** as in LLVM. Block arguments make a branch a jump that
  carries values, like a call, and need no rule that ties phis to
  predecessors.
