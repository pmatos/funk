# `fir-ref` decides dominance with a dominator tree placed by semidominators

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
dominance made `fir-ref validate` quadratic in the worst case.

A proof that an algorithm computes dominators must show that its tree's
ancestors are exactly the dominators. Checking a finished tree shows one
direction only: a tree whose every parent is an ancestor of each of its
predecessors has only dominators as ancestors, but a flatter tree can have
that property too, and miss dominators.

## Decision

- **`FirRef.problemsIn` replaces `Func.problemsIn`.** It is a copy of the
  spec's check, with copies of `siteDominates`, `useProblems` and
  `opProblems` that take the function deciding dominance as an argument.
  It answers a use defined in its own block or in the entry at once, since
  those dominate it, and every other use from the function's dominator
  tree (`FirRef.Dom.dominance`), which it builds once, when the first such
  use asks. `problemsIn_eq_problemsIn : @Func.problemsIn =
  @FirRef.problemsIn` is registered with `@[csimp]`, in a module that
  `FirRef.Validate` imports, so `FirRef.funcProblems` calls it.
- **The tree is built in four steps.** A depth-first search from the entry
  numbers the blocks and gives a spanning tree. Lengauer and Tarjan's
  algorithm, in its simple version with path compression, finds each
  block's semidominator. The semi-NCA placement then takes the blocks in
  increasing order of their numbers and moves each one from its tree parent
  up to the nearest ancestor of that parent numbered at most its
  semidominator; jump pointers make that walk logarithmic in the depth.
  Last, a check asks whether each block's parent is an ancestor of each of
  its predecessors. If the check ever failed, Cooper, Harvey and Kennedy's
  lifting would go on from the placed tree until no block moves.
- **The proof is an invariant of every move** (`FirRef.Dom.Lifted`): each
  block is numbered above its parent; each block is reached from its parent
  along a path of blocks numbered above that parent; and every block that
  is not an ancestor of `c` can be avoided on some path from the entry to
  `c`. The search's tree has all three. A placement move keeps them using
  one fact of the block's semidominator: it reaches the block along a path
  whose blocks after it are numbered at least as high as the block. Every
  candidate that Lengauer and Tarjan's algorithm compares has such a path,
  which is all that `Semis.run_spec` proves. A lifting move keeps them too.
  The check, or the lifting's end, gives the other direction: every path to
  a block passes through its ancestors. So the ancestors are the dominators
  (`Lifted.ancestor_iff`), and `dominance_eq` proves the answers equal to
  `dominatesIn` for every pair of labels.
- **A question walks up from the use's block**, by jump pointers chosen by
  the rule of Myers' skew-binary lists and otherwise by parents, so each
  question takes steps logarithmic in the depth of the tree. The proof
  needs only that each jump pointer is an ancestor.
- **The code lives in `lean/FirRef/Dominance.lean` and
  `lean/FirRef/Dominance/`.** Every loop is a tail call or a fold, so
  validation still takes no stack per block or per level of regions.

## Alternatives

- **One search per distinct dominating block, memoized.** A chain has a
  distinct dominating block per block, so the time stays quadratic.
- **Cooper, Harvey and Kennedy's lifting alone,** from the search's tree.
  The walks to common ancestors and the number of passes can each be
  linear in the number of blocks, even without loops: a chain of checks
  that may each branch to one shared exit took 50 s of CPU time at 32,768
  blocks, and a million would take hours.
- **Check a tree computed by unproved code, and fall back to the spec's
  search where the check fails.** The check gives only the ancestors that
  are dominators; a use whose definition does not dominate it would still
  cost a search, so an invalid function could still take quadratic time.
- **Prove Lengauer and Tarjan's theorems,** that the semidominators are
  exact and that the placement finds the immediate dominators, or certify
  the tree with a low-high order. Those proofs are longer than the
  invariant, and the check makes them unnecessary for correctness.

## Consequences

- The worst case, for a function whose entry reaches `n` blocks along `m`
  edges, with `U` uses defined in another block: the tree takes
  `O(m log n)` steps, each a hash-map operation. The search takes
  `O(n + m)`, the semidominators `O(m log n)` (the simple version of
  Lengauer and Tarjan's algorithm), the placement `O(n log n)` and the
  check `O(m log n)`, since each walk by jump pointers takes `O(log n)`
  steps. Each question takes `O(log n)` more, so dominance costs
  `O((m + U) log n)`, where the spec's search costs `O(U · (n + m))`.
- That bound rests on published results, not on proofs here: it holds when
  the semidominators are exact, so that the placement is the dominator
  tree and the check passes. The tests check that on every graph they
  try, so the lifting never runs. If it ever ran, it would have no such
  bound: its passes and walks can each be linear in the number of blocks.
- `fir-ref validate` checks a chain of a million blocks, each using the
  value of the block before it, in 19 to 34 seconds of CPU time, by the
  load on the machine, and a million blocks that may each leave for one
  shared exit in 25 to 42; the tree takes a third of each or a little
  more. The spec's search takes hours on both.
  `scripts/check-fir-ref.sh test` runs them under soft limits of 180 and
  240 seconds of CPU time, at least 5 times the slowest of those times.
- A function whose uses are all defined in their own block or in the entry
  never builds the tree, so it costs what the spec's check costs.
- A change to the spec's `Func.problemsIn`, `opProblems`, `useProblems` or
  `siteDominates` breaks `problemsIn_eq_problemsIn` until the copies follow.
