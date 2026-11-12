# Every block of a fir function is reachable from its entry

Status: accepted
Tier: direction; area: validation

## Decision

- Validation rejects a function with a block that its entry does not reach
  (`reachable` in `Func.Valid`, `lean/Fir/Validation/Rules.lean`). The
  verifier names the block in its reason. The spec proves the rejection
  (`deadBlock_rejected`, `lean/Fir/Core/Rejects.lean`).
- Dominance has its standard meaning: block `a` dominates block `b` when
  every path from the entry to `b` passes through `a`. It needs no case
  for unreachable blocks, and definitions cannot form a cycle.
- Producers, frontends and passes alike, delete unreachable blocks before
  validation. A pass that can leave a block unreachable, such as one that
  folds a branch, removes it before the IR is verified.

The human ruled this on 2026-10-30 (choice 20 in the
[rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
on #5, part 2).

## Why

Verifiers and passes may then assume that every block is reachable, and
that on every path from the entry a definition comes before its uses. No
tool has to cope with dead code whose definitions form a cycle, such as
block `U1` using `%b` from `U2` while `U2` uses `%a` from `U1`.

## Rejected alternatives

- **LLVM's rule:** accept unreachable blocks, dominated by every block. The
  fir v0 spec first followed it. Dead code could hold cyclic definitions,
  which every verifier and pass would have to tolerate.
