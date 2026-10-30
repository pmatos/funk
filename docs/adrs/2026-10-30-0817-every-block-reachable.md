# Every block of a fir function is reachable from its entry

Status: accepted

## Context

LLVM accepts blocks that the entry cannot reach, and counts them as
dominated by every block. In such dead blocks, values can be defined in a
cycle: block `U1` uses `%b` from `U2`, while `U2` uses `%a` from `U1`.
Every verifier and pass must then cope with that. The fir v0 spec first
followed LLVM. The human asked for a second opinion, and ruled on 2026-10-30
for the stricter rule (choice 20 in the [rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304) on #5, part 2).

## Decision

- Validation rejects a function with a block that its entry does not reach
  (`reachable` in `Func.Valid`, `lean/Fir/Validation/Rules.lean`). The
  verifier names the block in its reason.
- Dominance has its standard meaning: block `a` dominates block `b` when
  every path from the entry to `b` passes through `a`. It needs no case
  for unreachable blocks, and definitions cannot form a cycle.
- Producers, frontends and passes alike, delete unreachable blocks before
  validation.

## Alternatives

- **LLVM's rule:** accept unreachable blocks, dominated by every block.
  Rejected: dead code could hold cyclic definitions, which every verifier and
  pass would have to tolerate.

## Consequences

- Verifiers and passes may assume that every block is reachable, and that on
  every path from the entry a definition comes before its uses.
- A pass that can leave a block unreachable, such as one that folds a branch,
  removes the block before the IR is verified.
- The spec proves that validation rejects a function with an unreachable
  block (`deadBlock_rejected`, `lean/Fir/Core/Rejects.lean`). #9's verifier
  and #19 add the same must-reject test.
