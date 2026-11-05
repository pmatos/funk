# `fir-ref` checks a location table with core's loops in place of `List.zip` and `List.decidableBAll`

Status: accepted

## Context

fir has no nesting limit, and no limit on the size of a location table
(ADR-2026-10-30-1549): `fir-ref validate` must give its verdict on any
table. ADR-2026-10-30-1742 made its walk of nested blocks take no stack per
level. The check of the location table, `LocTable.problems`
([`CheckModule.lean`](../../lean/Fir/Validation/CheckModule.lean)), walks
flat lists only, yet compiled it took stack in two places
([#136](https://github.com/pmatos/funk/issues/136)):

- `keys.zip keys.tail` calls core's `List.zip`. Core compiles `List.zip`
  before its `@[csimp]` theorem `List.zipWith_eq_zipWithTR`, so the call
  runs core's recursive `List.zipWith`: one frame per entry of the table.
- `∀ n ∈ l.numbers, n < Location.limit` is decided by core's instance
  `List.decidableBAll`, which recurses once per element: one frame per
  reference of a fused location.

With `LEAN_STACK_SIZE_KB=256`, `fir-ref validate` aborted with "Stack
overflow detected" on a table of 1,000,000 entries and on a fused location
of 1,000,000 references. ADR-2026-10-30-1450 gives the way out: `fir-ref`
runs an implementation proved equal to the spec's function and registered
with `@[csimp]`, and the spec keeps its definition.

## Decision

- **`FirRef.locTableProblems`**
  ([`lean/FirRef/LocTable.lean`](../../lean/FirRef/LocTable.lean)) is the
  spec's check with two changes: `List.zipWith Prod.mk keys keys.tail` in
  place of `keys.zip keys.tail`, and the Boolean
  `r < Location.limit && l.numbers.all (· < Location.limit)` in place of
  the proposition that `List.decidableBAll` decides. `List.zipWith`
  compiles to core's loop `List.zipWithTR`, and `List.all` is a loop.
  Every other step is a loop already: `List.map`, `List.filterMap`,
  `List.flatMap`, `List.length` and `++` through core's `@[csimp]`
  theorems, and `Std.HashSet.ofList` through a loop of core's.
- **`problems_eq_locTableProblems : @LocTable.problems =
  @locTableProblems`** is proved by `simp only` with the definition of
  `List.zip` and the lemmas `Bool.and_eq_true`, `decide_eq_true_eq` and
  `List.all_eq_true`, rests on Lean's standard axioms, and is registered
  with `@[csimp]`.
- **`FirRef.Validate` imports `FirRef.LocTable`,** so `moduleProblems`,
  and its copy specialized to the core dialect in `FirRef.reportModule`,
  call `locTableProblems`. `FirRef.Fast` lists it with the other modules
  that register such a theorem.
- **Tests.** [`lean/FirTest/LocTable.lean`](../../lean/FirTest/LocTable.lean)
  checks a table of 1,000,000 entries and a fused location of 1,000,003
  references, each with errors at the start, in the middle and at the end,
  through `LocTable.problems`, `Module.problems`, `decide` and
  `FirRef.reportModule`. They check the answers at that size, not the
  stack: the elaborator's stack is large, and the spec's recursions run in
  core's compiled code, whose frames are small, so the spec's check passes
  them too. Run by `lean` on 2026-11-05, it passed with the default stack,
  and aborted with a `--tstack` of 65,536 KiB or less on the entries, and
  of 16,384 KiB or less on the references. So `scripts/check-fir-ref.sh test` checks the stack:
  `fir-ref validate`, with `LEAN_STACK_SIZE_KB=256`, accepts a table of
  1,000,000 entries and a fused location of 1,000,000 references. The
  readers of #47 (PR #133) read both texts on that stack; with them alone,
  `fir-ref fmt --check` accepted both, and `fir-ref validate` aborted on
  both.

## Alternatives

- **Change the spec's check.** The spec keeps its readable definition
  (ADR-2026-10-30-1450), and `pairwise_lt_iff_zip` states the order of
  references with `List.zip`.
- **A loop of its own, with an accumulator.** Core's loops already take no
  stack, and the proof would be longer.
- **An instance for `∀ x ∈ l, p x` of high priority in `lean/FirRef/`.**
  It would change how every module that imports it decides such a
  proposition, for one use.

## Consequences

- `fir-ref validate` checks a location table with no stack per entry or
  per reference, and gives the spec's answer, byte for byte. Its CPU time
  does not change.
- `List.zip` and a decision of `∀ x ∈ l, p x` by its instance take stack
  per element of `l` in compiled code. Code in `lean/FirRef/` that walks a
  list whose length the input sets uses `List.zipWith` and `List.all`
  instead.
- A change to `LocTable.problems` breaks `problems_eq_locTableProblems`,
  and so the build, until `locTableProblems` follows it.
