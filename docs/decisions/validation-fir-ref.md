# Current decisions: validation in `fir-ref`

This page continues validation.md. It says how `fir-ref` runs the spec's
validation check at any depth. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## How `fir-ref` runs the check

fir has no nesting limit. Every tool handles any depth without a stack
overflow, on a small stack too (ADR-2026-10-30-1549). The spec keeps its
readable definitions. `fir-ref` runs implementations proved equal to them and
registered with `@[csimp]` (ADR-2026-10-30-1450).

`FirRef.moduleProblems` and `FirRef.funcProblems`, in
`lean/FirRef/Validate.lean`, are copies of `Module.problems` and
`Func.problems`. They are compiled after the theorems that replace the spec's
parts, and registered with `@[csimp]` by `rfl`. So `fir-ref`'s calls of the
spec's two functions reach the copies and never the spec's walk.

Rejected: writing the spec's check with an explicit stack. The spec would lose
its readable definition of a function's blocks (ADR-2026-10-30-1450).

Four parts of the check are replaced:

- **Nested blocks.** `FirRef.allBlocks` lists the same blocks as
  `Func.allBlocks`, with an explicit stack of frames. `allBlocks_eq_allBlocks`
  proves them equal.
- **Uses and dominance.** `FirRef.problemsIn` replaces `Func.problemsIn`
  (see [Dominance in `fir-ref`](#dominance-in-fir-ref)).
- **The location table.** `FirRef.locTableProblems` replaces
  `LocTable.problems` (see [Location tables](#location-tables)).
- **Symbol tables.** `FirRef.tablesIn`, in `lean/FirRef/Tables.lean`, lists
  the same tables as `Item.tablesIn`, with an explicit stack of lists of
  items. `tablesIn_eq_tablesIn` proves them equal, and `@[csimp]` registers
  it, as for blocks. `lean/FirTest/ValidateNested.lean`
  checks modules nested 1,000,000 deep, and `scripts/check-fir-ref-deep.sh`
  has `fir-ref validate` accept one on a 256 KiB stack
  (ADR-2026-10-30-1549, ADR-2026-11-10-1510).

Validation takes no stack per block or per level of regions.
`lean/FirTest/Validate.lean` checks modules with regions nested 1,000,000
deep. Without the `@[csimp]`, its build aborts with a stack overflow. No
specific depth is an M0 acceptance bar: the human ruled that on 2026-10-30,
on #47 (comment 6530544151).

Some rules reach into regions, such as H6's scoping of values in regions. Such
a rule takes its blocks from the list that `Func.problemsIn` is given.
Otherwise it brings a loop of its own with a `@[csimp]` theorem.

## `decide` on validity

`fir-ref` may decide validity with `decide`, in a module that imports
`FirRef.Fast`. `fir-ref validate` still calls `Module.problems`, because it
reports each problem, not only the verdict.

Two instances of priority `high` make that work at any depth. They sit in
`lean/FirRef/Validate.lean`, after `problems_eq_moduleProblems`.
`FirRef.decidableValid` is for `Decidable m.Valid`. `FirRef.decidableFuncValid`
is for `Decidable (f.Valid ctx)`. Their code calls `FirRef.moduleProblems` and
`FirRef.funcProblems`. The spec's own instances are compiled before any
theorem of `lean/FirRef/`, so without these, `decide` would run the spec's
walk and take stack per level of regions.

Each instance is the spec's instance word for word. `decidableValid_eq` and
`decidableFuncValid_eq` prove them equal to the spec's by `rfl`, on Lean's
standard axioms only. So a proof by
`decide` unfolds the same definition as with the spec's instance.

`FirRef.Fast` imports `FirRef.Validate`. So every module that imports
`FirRef.Fast` resolves `decide m.Valid`, `if m.Valid then ...` and
`decide (f.Valid ctx)` to these instances. `FirRef.Main` and `FirTest` are among
them. There, `decide` gives the spec's answer and takes no stack per level of
regions. In a module that imports neither `FirRef.Fast` nor `FirRef.Validate`,
`decide` still runs the spec's walk (ADR-2026-10-30-1450).

A `@[csimp]` theorem on the spec's instance would also work, at each use
compiled after it. The instances were chosen because `#synth` can pin them in
a test that needs no run at depth. Rejected too: a rule that `fir-ref` never
uses `decide` on validity. It is a trap: a later `if m.Valid` would take stack
per level, and no test would catch it. Compiling the spec's instances after
the theorems cannot be done: the spec cannot import `lean/FirRef/`, which
imports it.

`lean/FirTest/Validate.lean` pins the instances that `#synth` finds. It also
runs `decide` on a module nested 1,000,000 levels deep. That module is not
valid. No valid core module nests regions, since no core op owns one
(ADR-2026-11-10-1941).

## Dominance in `fir-ref`

The spec decides dominance with a fresh search of the function's graph, for
each use defined in another block. That search is `dominatesIn`, in
`lean/Fir/Validation/Graph.lean`. The spec keeps it, and `fir-ref` replaces it
(#55).

`FirRef.problemsIn` is a copy of the spec's check. Its copies of
`siteDominates`, `useProblems` and `opProblems` take the function deciding
dominance as an argument. It answers a use defined in its own block or in the
entry at once. Every other use is answered from the function's dominator tree,
`FirRef.Dom.dominance`. The tree is built once, when the first such use asks.

`problemsIn_eq_problemsIn` proves the copy equal to `Func.problemsIn`. It is
registered with `@[csimp]`, in a module that `FirRef.Validate` imports.

The tree is built in four steps:

1. A depth-first search from the entry numbers the blocks and gives a spanning
   tree.
2. Lengauer and Tarjan's algorithm finds each block's semidominator. It is the
   simple version, with path compression.
3. The semi-NCA placement takes the blocks in increasing order of their
   numbers. It moves each one up from its tree parent. It stops at the nearest
   ancestor of that parent numbered at most its semidominator. Jump pointers
   make that walk logarithmic in the depth.
4. A check asks whether each block's parent is an ancestor of each of its
   predecessors. If it ever failed, Cooper, Harvey and Kennedy's lifting would
   go on from the placed tree until no block moves.

The proof is an invariant of every move, `FirRef.Dom.Lifted`. It has three
parts:

- Each block is numbered above its parent.
- Each block is reached from its parent along a path of blocks numbered above
  that parent.
- Every block that is not an ancestor of `c` can be avoided on some path from
  the entry to `c`.

The check, or the end of the lifting, gives the other direction. Every path to
a block passes through its ancestors. So the ancestors are the dominators
(`Lifted.ancestor_iff`). `dominance_eq` proves the answers equal to
`dominatesIn` for every pair of labels.

A question walks up from the use's block. It goes by jump pointers, chosen by
the rule of Myers' skew-binary lists, and otherwise by parents. Each question
takes steps logarithmic in the depth of the tree. The code lives in
`lean/FirRef/Dominance.lean` and `lean/FirRef/Dominance/`. Every loop is a tail
call or a fold, so validation still takes no stack per block or per level of
regions.

Take a function whose entry reaches `n` blocks along `m` edges, with `U` uses
defined in another block. Dominance costs `O((m + U) log n)`. The spec's search
costs `O(U * (n + m))`. That bound rests on published results, not on proofs
here. It holds when the semidominators are exact, so that the placement is the
dominator tree and the check passes. The tests check that on every graph they
try, so the lifting never runs. If it ever ran, it would have no such bound.

A function whose uses are all defined in their own block or in the entry never
builds the tree. It costs what the spec's check costs. A function with one or a
few uses defined elsewhere pays for the whole tree.

Rejected: Cooper, Harvey and Kennedy's lifting alone, from the search's tree.
Its walks and passes can each be linear in the number of blocks: a chain of
checks that may each branch to one shared exit took 50 seconds of CPU time at
32,768 blocks. Rejected too: a memoized search per dominating block, which
stays quadratic on a chain, and checking a tree of unproved code with the
spec's search as a fallback, which stays quadratic on invalid functions.
Proving Lengauer and Tarjan's theorems, or certifying the tree with a
low-high order, was rejected too: those proofs are longer than the
invariant, and the check makes them unnecessary for correctness.

`scripts/check-fir-ref.sh test` runs two cases of a million blocks under soft
limits of CPU time. A chain, each block using the value of the block before it,
has 180 seconds. Blocks that may each leave for one shared exit have 240
seconds. The script's comment gives their light-load times.

## Location tables

The spec limits only the numbers of a location table (N3, `Location.limit`). It
does not limit how many entries a table has, or how many references a fused
location holds. So `fir-ref validate` gives its verdict on any table (#136).

`FirRef.locTableProblems`, in `lean/FirRef/LocTable.lean`, is the spec's
`LocTable.problems` with two changes. `List.zipWith Prod.mk keys keys.tail`
stands in place of `keys.zip keys.tail`. A Boolean built with `List.all` stands
in place of the proposition that `List.decidableBAll` decides.

`problems_eq_locTableProblems` proves the two equal and rests on Lean's standard
axioms. It is registered with `@[csimp]`. `FirRef.Fast` lists its module with
the other modules that register such a theorem.

`FirRef.Validate` imports `FirRef.LocTable`. So `moduleProblems` calls
`locTableProblems`, and so does its copy specialized to the core dialect in
`FirRef.reportModule`. `fir-ref validate` checks a location table with no stack
per entry or per reference. It gives the spec's answer, byte for byte.

Rejected: an instance of high priority for `∀ x ∈ l, p x` in `lean/FirRef/`.
It would change how every module that imports it decides such a proposition,
for one use. Rejected too: changing the spec's check, which keeps its
readable definition (`pairwise_lt_iff_zip` states the order of references
with `List.zip`), and a loop of its own with an accumulator, since core's
loops already take no stack and the proof would be longer.

`lean/FirTest/LocTable.lean` checks a table of 1,000,000 entries and a fused
location of 1,000,003 references. Each has errors at the start, in the middle
and at the end. They run through `LocTable.problems`, `Module.problems`,
`decide` and `FirRef.reportModule`. These tests check the answers at that size,
not the stack.

`scripts/check-fir-ref.sh test` checks the stack. With
`LEAN_STACK_SIZE_KB=256`, `fir-ref validate` accepts a table of 1,000,000
entries and a fused location of 1,000,000 references.

In compiled code, `List.zip` takes stack per element. So does deciding a
for-all or an exists over a list with core's instances, `List.decidableBAll`
and `List.decidableBEx`. Code in `lean/FirRef/` that walks a list whose length
the input sets calls none of them. It uses `List.zipWith`, `List.all` and
`List.any`, or a loop of its own that takes no stack per element.

## Keeping the copies in step

A change to a spec function breaks its theorem's proof, and so the build, until
the implementation follows it (ADR-2026-10-30-1450). For validation, that means:

- A change to `Func.problemsIn`, `opProblems`, `useProblems` or `siteDominates`
  breaks `problemsIn_eq_problemsIn`.
- A change to either spec instance of `Decidable` for validity breaks `rfl` in
  its theorem.
- A change to `LocTable.problems` breaks `problems_eq_locTableProblems`.
