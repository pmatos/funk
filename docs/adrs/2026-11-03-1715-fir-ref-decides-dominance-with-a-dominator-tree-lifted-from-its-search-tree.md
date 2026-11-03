# `fir-ref` decides dominance with a dominator tree that it lifts from its search tree once per function

Status: accepted

## Context

The spec's validation check decides `Func.Dominates a l` for each use whose
definition is in another block with a fresh search of the function's graph
(`dominatesIn`, `lean/Fir/Validation/Graph.lean`). A function of `V` blocks
with `U` such uses takes time in `O(U · V)`: a valid chain of a million
blocks, each using the value of the block before it, does not finish
([#55](https://github.com/pmatos/funk/issues/55)). The spec keeps that
readable search. ADR-2026-10-30-1450 gives the way `fir-ref` runs code
proved equal to a spec function, and ADR-2026-10-30-1742 records that
dominance was the check's one quadratic part.

A proof that an algorithm computes dominators must show that its tree's
ancestors are exactly the dominators. Checking a finished tree shows one
direction only: a tree whose every parent is an ancestor of each of its
predecessors has only dominators as ancestors, but a flatter tree can have
that property too, and miss dominators.

## Decision

- **`FirRef.problemsIn` replaces `Func.problemsIn`.** It is a copy of the
  spec's check, with copies of `siteDominates`, `useProblems` and
  `opProblems` that take the function deciding dominance as an argument.
  It builds the function's dominator tree once (`FirRef.dominance`) and
  answers every use from it. `problemsIn_eq_problemsIn : @Func.problemsIn =
  @FirRef.problemsIn` is registered with `@[csimp]`, in a module that
  `FirRef.Validate` imports, so `FirRef.funcProblems` calls it.
- **The tree starts as the depth-first search tree from the entry and is
  lifted.** A block whose parent is not an ancestor of each of its
  predecessors moves to their nearest common ancestor; passes repeat until
  one moves nothing. This is the iterative algorithm of Cooper, Harvey and
  Kennedy that `funk verify` uses, started from the search's tree instead
  of from no tree.
- **The proof is an invariant of the lifting** (`FirRef.Lifted`): each
  block is numbered above its parent; each block is reached from its parent
  along a path of blocks numbered above that parent; and every block that
  is not an ancestor of `c` can be avoided on some path from the entry to
  `c`. The search's tree has all three, and each move keeps them. When no
  block moves, every path to a block passes through its ancestors. So the
  ancestors are the dominators (`Lifted.ancestor_iff`), and `dominance_eq`
  proves the answers equal to `dominatesIn` for every pair of labels. A pass that
  moves a block lowers the sum of the numbers of the blocks' parents, which
  gives the passes a measure; no fuel.
- **A question walks up from the use's block**, by jump pointers chosen by
  the rule of Myers' skew-binary lists and otherwise by parents, so each
  question takes steps logarithmic in the depth of the tree. The proof
  needs only that each jump pointer is an ancestor.
- **The code lives in `lean/FirRef/Dominance.lean` and
  `lean/FirRef/Dominance/`.** Every loop is a tail call or a core list
  function compiled as one, so validation still takes no stack per block or
  per level of regions.

## Alternatives

- **One search per distinct dominating block, memoized.** A chain has a
  distinct dominating block per block, so the time stays quadratic.
- **Check a tree computed by unproved code, and fall back to the spec's
  search where the check fails.** The check gives only the ancestors that
  are dominators; a use whose definition does not dominate it would still
  cost a search, so an invalid function could still take quadratic time.
- **Lengauer and Tarjan's algorithm, or a low-high order as a certificate.**
  Their proofs need semidominators or a construction of the order, which
  are longer than the lifting's three facts.

## Consequences

- `fir-ref validate` checks a chain of a million blocks in about 20 seconds
  of CPU time, most of it outside dominance. `scripts/check-fir-ref.sh
  test` runs that chain under a soft limit of 120 seconds of CPU time.
- Like Cooper, Harvey and Kennedy's algorithm, the lifting has no linear
  bound: the number of passes and the length of each walk to a common
  ancestor depend on the graph's loops. A chain takes one pass, and a
  branch that joins again takes two.
- A change to the spec's `Func.problemsIn`, `opProblems`, `useProblems` or
  `siteDominates` breaks `problemsIn_eq_problemsIn` until the copies follow.
