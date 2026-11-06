# A by_cases on a proposition without a Decidable instance runs under classical

Status: accepted

## Context

`by_cases h : p` expands to `open Classical in refine if h : p then ?pos
else ?neg`. When `p` has no `Decidable` instance, the proof relies on
`Classical.propDecidable`, a scoped instance that `open Classical` turns
on. `open` turns on scoped instances through a process-wide list of scoped
extensions.

`lean/` sets `doc.verso` ([lakefile.lean](../../lean/lakefile.lean)).
In Lean v4.35.0, our pinned toolchain, Verso elaborates each module
docstring with that list swapped for an empty one, on the main thread.
Theorem proofs elaborate on other threads at the same time. A `by_cases`
that runs during the swap turns on nothing and fails with "failed to
synthesize Decidable p". This is Lean issue
[leanprover/lean4#15817](https://github.com/leanprover/lean4/issues/15817).
It made one Pages build of `main` fail at `FirRef/Dominance/Lift.lean`
([#184](https://github.com/pmatos/funk/issues/184)). The fix,
[leanprover/lean4#15839](https://github.com/leanprover/lean4/pull/15839)
(commit `541dbdcd`), is in no release yet.

## Decision

- Every `by_cases` under `lean/` whose proposition has no `Decidable`
  instance has the `classical` tactic before it, in the same tactic block.
- `classical` adds `Classical.propDecidable` as a local instance without
  the process-wide list, so the outcome cannot depend on the race.
- A `by_cases` whose proposition has an instance, such as `x = y` on
  `Name`, stays as it is: it never needs the scoped instance.

## Alternatives

- `rcases Classical.em p with h | h`: also safe, but it names the goals
  `inl` and `inr`, and two proofs select the goal `neg`.
- Turning `doc.verso` off: the spec renders our docstrings as Verso.

## Consequences

- The `classical` lines look redundant. Do not remove them while the
  toolchain lacks `541dbdcd`; once it has it, they may go.
- A new `by_cases` on such a proposition needs `classical` too. A missing
  one fails at random, not every build.
