# Current decisions: validation

This page states what holds today for validation in fir and in `fir-ref`. It
summarizes the ADRs it cites (ADR-2026-11-09-1610). If this page and an ADR
disagree, the page has a bug.

## Rules of validity

Every block of a fir function is reachable from its entry. Validation rejects
a function with a block that its entry does not reach. The verifier names that
block in its reason. The rule is `reachable` in `Func.Valid`, in
`lean/Fir/Validation/Rules.lean`. The spec proves the rejection as
`deadBlock_rejected`, in `lean/Fir/Core/Rejects.lean` (ADR-2026-10-30-0817).

Dominance has its standard meaning. Block `a` dominates block `b` when every
path from the entry to `b` passes through `a`. It needs no case for
unreachable blocks. Definitions cannot form a cycle (ADR-2026-10-30-0817).

Producers delete unreachable blocks before validation. That covers frontends
and passes alike. A pass can leave a block unreachable, say by folding a
branch. It then removes the block before the IR is verified. Verifiers and
passes may assume that every block is reachable. They may also assume that a
definition comes before its uses on every path from the entry
(ADR-2026-10-30-0817).

## The spec's check

The spec has an executable check, `Module.problems`, in
`lean/Fir/Validation/CheckModule.lean`. It takes two things from a dialect,
and nothing more (ADR-2026-10-30-1740):

- `[DecidableEq d.Ty]`, the standard class.
- An instance of `DecidableDialectValidation d`, from
  `lean/Fir/Validation/Check.lean`. Its fields decide `validTy t` for every
  type, `validOp ctx o` for every context and op, and `validFunc` for every
  function (ADR-2026-11-09-2257).

A module's dialect set has a rule of its own, `Module.InDialectSet`, in
`lean/Fir/Validation/DialectSet.lean`, beside `Module.Valid`. It reads the
module's words through the dialect's text, so `Module.Valid` and the
theorems about it need no text. Its check is `Module.setProblems`, and
`fir-ref validate` and `funk verify` report `Module.problems`, then
`Module.setProblems` (ADR-2026-11-10-1306).

A dialect's rules in `DialectValidation` stay propositions. A dialect that
wants the check proves them decidable. The core dialect does so case by case
in `lean/Fir/Core/Check.lean`. A new dialect derives `DecidableEq` for its
types and decides its three rules. It then gets the check, and so `fir-ref
validate` (ADR-2026-10-30-1740).

The check agrees with the rules in both directions. `Module.problems_eq_nil_iff`
proves that a module has no problems exactly when it is valid. That gives the
instance `Decidable m.Valid` (ADR-2026-10-30-1740).

A dialect gives no reason when its own rule fails. The check says that the op
breaks its dialect's own rule, and gives the op's index and block. Messages
about a type or a dialect rule print neither the type nor the op instance.
They name the value, the op's index and its block (ADR-2026-10-30-1740).

The spec's check walks nested blocks once. `Func.problems` calls
`Func.allBlocks` and passes the list to `Func.problemsIn`. `Func.problemsIn`
reads no other nested part of a function (ADR-2026-10-30-1742).

## A dialect's rule over a function

A dialect may add a rule over a whole function, for what no op can see alone,
such as a value that must be used exactly once. In Lean it is `validFunc`, and
`Func.Valid` requires it. In `funk-ir` a dialect registers a `FuncSpec`, and
`verify` runs every registered rule. The core dialect has no such rule
(ADR-2026-11-09-2257).

The Lean rule sees the function of the host dialect through a
`DialectView`, which maps each host op and type to the dialect's own or to
`none`. So a rule is written once and holds in any sum of dialects. It reads
only the module's symbol table, and it must assume nothing about the function,
because validation calls it on every function (ADR-2026-11-09-2257).

A broken function rule is reported at the function's entry block, with the
location of its first op. `tests/dialects/use-once.cases` holds the cases of a
use-once toy dialect, which the Lean and Rust tests both read
(ADR-2026-11-09-2257).

## A base op in a sum of dialects

In the spec's sum `base ⊞ e`, a base op is checked by the base's own rule.
It sees only the symbols whose types are all the base's. It sees the
function's result types only when they are all the base's. Otherwise no base
op is valid in that function, `add` included. Dropping the types that the
base cannot write would let a core `ret` return too few values
(ADR-2026-11-09-2353).

An extension lifted into a larger sum follows the same rule against what it
depends on. Its op sees only the symbols whose types are all its own or its
dependencies', and is valid only where the function's result types all are
(ADR-2026-11-10-1310).

## Region kinds

An op instance states the kinds of the regions its op owns, each a word of
a dialect, never the core's: a region of the core's kind inside an op would
be structured control flow, which M1 leaves out. A dialect registers kinds,
each with a rule over a region of the function, seen through a view as a
function rule is. The rule says how values are scoped in the region, which
ops end its blocks and where its successors go. An op is valid only when its
regions have the kinds its op instance states, each registered, and each
obeys its rule. The core registers no kind, and its own kind's rule is the
rule of a function's body (ADR-2026-11-10-1941).

An op inside a region obeys the general rules that hold whatever the kind:
its regions, types, number of successors, symbols, its dialect's own rule
and its location; a successor's label is a name and the values it passes
are defined in the function. The check walks the function's blocks at any
depth and each op's own regions, one level down, so it takes no stack per
level (ADR-2026-11-10-1941).

In a sum, a region of a kind that the base registers obeys the base's rule,
and any other kind `e`'s rule. A dialect writes its kinds under its name, so
each kind goes to the dialect that registers it. A lift registers `e`'s
kinds. In `funk-ir`, a dialect registers a `RegionKindSpec`, under its
prefix (ADR-2026-11-10-1941).

## How `fir-ref` runs the check

fir has no nesting limit. Every tool handles any depth without a stack
overflow, on a small stack too (ADR-2026-10-30-1549). The spec keeps its
readable definitions. `fir-ref` runs implementations proved equal to them and
registered with `@[csimp]` (ADR-2026-10-30-1450).

`FirRef.moduleProblems` and `FirRef.funcProblems`, in
`lean/FirRef/Validate.lean`, are copies of `Module.problems` and
`Func.problems`. They are compiled after the theorems that replace the spec's
parts, and registered with `@[csimp]` by `rfl`. So `fir-ref`'s calls of the
spec's two functions reach the copies and never the spec's walk
(ADR-2026-10-30-1742).

Three parts of the check are replaced:

- **Nested blocks.** `FirRef.allBlocks` lists the same blocks as
  `Func.allBlocks`, with an explicit stack of frames. `allBlocks_eq_allBlocks`
  proves them equal (ADR-2026-10-30-1742).
- **Uses and dominance.** `FirRef.problemsIn` replaces `Func.problemsIn`
  (ADR-2026-11-03-1715).
- **The location table.** `FirRef.locTableProblems` replaces
  `LocTable.problems` (ADR-2026-11-05-0745).

Validation takes no stack per block or per level of regions
(ADR-2026-11-03-1715). `lean/FirTest/Validate.lean` checks modules with regions
nested 1,000,000 deep. Without the `@[csimp]`, its build aborts with a stack
overflow. No specific depth is an M0 acceptance bar (ADR-2026-10-30-1742).

Some rules reach into regions, such as H6's scoping of values in regions. Such
a rule takes its blocks from the list that `Func.problemsIn` is given.
Otherwise it brings a loop of its own with a `@[csimp]` theorem
(ADR-2026-10-30-1742).

## `decide` on validity

`fir-ref` may decide validity with `decide`, in a module that imports
`FirRef.Fast`. `fir-ref validate` still calls `Module.problems`, because it
reports each problem, not only the verdict (ADR-2026-11-05-0025).

Two instances of priority `high` make that work at any depth. They sit in
`lean/FirRef/Validate.lean`, after `problems_eq_moduleProblems`.
`FirRef.decidableValid` is for `Decidable m.Valid`. `FirRef.decidableFuncValid`
is for `Decidable (f.Valid ctx)`. Their code calls `FirRef.moduleProblems` and
`FirRef.funcProblems` (ADR-2026-11-05-0025).

Each instance is the spec's instance word for word. `decidableValid_eq` and
`decidableFuncValid_eq` prove them equal to the spec's by `rfl`. So a proof by
`decide` unfolds the same definition as with the spec's instance
(ADR-2026-11-05-0025).

`FirRef.Fast` imports `FirRef.Validate`. So every module that imports
`FirRef.Fast` resolves `decide m.Valid`, `if m.Valid then ...` and
`decide (f.Valid ctx)` to these instances. `FirRef.Main` and `FirTest` are among
them. There, `decide` gives the spec's answer and takes no stack per level of
regions. In a module that imports neither `FirRef.Fast` nor `FirRef.Validate`,
`decide` still runs the spec's walk (ADR-2026-11-05-0025).

A `@[csimp]` theorem on the spec's instance would also work, at each use
compiled after it. The instances were chosen because `#synth` can pin them in
a test that needs no run at depth (ADR-2026-11-05-0025).

`lean/FirTest/Validate.lean` pins the instances that `#synth` finds. It also
runs `decide` on a module nested 1,000,000 levels deep. That module is not
valid. No valid core module nests regions, since no core op owns one
(ADR-2026-11-05-0025, ADR-2026-11-10-1941).

## Dominance in `fir-ref`

The spec decides dominance with a fresh search of the function's graph, for
each use defined in another block. That search is `dominatesIn`, in
`lean/Fir/Validation/Graph.lean`. The spec keeps it, and `fir-ref` replaces it
(ADR-2026-11-03-1715).

`FirRef.problemsIn` is a copy of the spec's check. Its copies of
`siteDominates`, `useProblems` and `opProblems` take the function deciding
dominance as an argument. It answers a use defined in its own block or in the
entry at once. Every other use is answered from the function's dominator tree,
`FirRef.Dom.dominance`. The tree is built once, when the first such use asks
(ADR-2026-11-03-1715).

`problemsIn_eq_problemsIn` proves the copy equal to `Func.problemsIn`. It is
registered with `@[csimp]`, in a module that `FirRef.Validate` imports
(ADR-2026-11-03-1715).

The tree is built in four steps (ADR-2026-11-03-1715):

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
parts (ADR-2026-11-03-1715):

- Each block is numbered above its parent.
- Each block is reached from its parent along a path of blocks numbered above
  that parent.
- Every block that is not an ancestor of `c` can be avoided on some path from
  the entry to `c`.

The check, or the end of the lifting, gives the other direction. Every path to
a block passes through its ancestors. So the ancestors are the dominators
(`Lifted.ancestor_iff`). `dominance_eq` proves the answers equal to
`dominatesIn` for every pair of labels (ADR-2026-11-03-1715).

A question walks up from the use's block. It goes by jump pointers, chosen by
the rule of Myers' skew-binary lists, and otherwise by parents. Each question
takes steps logarithmic in the depth of the tree. The code lives in
`lean/FirRef/Dominance.lean` and `lean/FirRef/Dominance/`. Every loop is a tail
call or a fold (ADR-2026-11-03-1715).

Take a function whose entry reaches `n` blocks along `m` edges, with `U` uses
defined in another block. Dominance costs `O((m + U) log n)`. The spec's search
costs `O(U * (n + m))`. That bound rests on published results, not on proofs
here. It holds when the semidominators are exact, so that the placement is the
dominator tree and the check passes. The tests check that on every graph they
try, so the lifting never runs. If it ever ran, it would have no such bound
(ADR-2026-11-03-1715).

A function whose uses are all defined in their own block or in the entry never
builds the tree. It costs what the spec's check costs. A function with one or a
few uses defined elsewhere pays for the whole tree (ADR-2026-11-03-1715).

`scripts/check-fir-ref.sh test` runs two cases of a million blocks under soft
limits of CPU time. A chain, each block using the value of the block before it,
has 180 seconds. Blocks that may each leave for one shared exit have 240
seconds (ADR-2026-11-03-1715).

## Location tables

The spec limits only the numbers of a location table (N3, `Location.limit`). It
does not limit how many entries a table has, or how many references a fused
location holds. So `fir-ref validate` gives its verdict on any table
(ADR-2026-11-05-0745).

`FirRef.locTableProblems`, in `lean/FirRef/LocTable.lean`, is the spec's
`LocTable.problems` with two changes. `List.zipWith Prod.mk keys keys.tail`
stands in place of `keys.zip keys.tail`. A Boolean built with `List.all` stands
in place of the proposition that `List.decidableBAll` decides
(ADR-2026-11-05-0745).

`problems_eq_locTableProblems` proves the two equal and rests on Lean's standard
axioms. It is registered with `@[csimp]`. `FirRef.Fast` lists its module with
the other modules that register such a theorem (ADR-2026-11-05-0745).

`FirRef.Validate` imports `FirRef.LocTable`. So `moduleProblems` calls
`locTableProblems`, and so does its copy specialized to the core dialect in
`FirRef.reportModule`. `fir-ref validate` checks a location table with no stack
per entry or per reference. It gives the spec's answer, byte for byte
(ADR-2026-11-05-0745).

`lean/FirTest/LocTable.lean` checks a table of 1,000,000 entries and a fused
location of 1,000,003 references. Each has errors at the start, in the middle
and at the end. They run through `LocTable.problems`, `Module.problems`,
`decide` and `FirRef.reportModule`. These tests check the answers at that size,
not the stack (ADR-2026-11-05-0745).

`scripts/check-fir-ref.sh test` checks the stack. With
`LEAN_STACK_SIZE_KB=256`, `fir-ref validate` accepts a table of 1,000,000
entries and a fused location of 1,000,000 references (ADR-2026-11-05-0745).

In compiled code, `List.zip` takes stack per element. So does deciding a
for-all or an exists over a list with core's instances, `List.decidableBAll`
and `List.decidableBEx`. Code in `lean/FirRef/` that walks a list whose length
the input sets calls none of them. It uses `List.zipWith`, `List.all` and
`List.any`, or a loop of its own that takes no stack per element
(ADR-2026-11-05-0745).

## Keeping the copies in step

A change to a spec function breaks its theorem's proof, and so the build, until
the implementation follows it (ADR-2026-10-30-1450). For validation, that means:

- A change to `Func.problemsIn`, `opProblems`, `useProblems` or `siteDominates`
  breaks `problemsIn_eq_problemsIn` (ADR-2026-11-03-1715).
- A change to either spec instance of `Decidable` for validity breaks `rfl` in
  its theorem (ADR-2026-11-05-0025).
- A change to `LocTable.problems` breaks `problems_eq_locTableProblems`
  (ADR-2026-11-05-0745).
