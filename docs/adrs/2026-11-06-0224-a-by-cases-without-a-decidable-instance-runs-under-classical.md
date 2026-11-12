# A by_cases on a proposition without a Decidable instance runs under classical

Status: accepted
Tier: direction; area: spec-site

## Decision

- Every `by_cases` under `lean/` whose proposition has no `Decidable`
  instance has the `classical` tactic before it, in the same tactic block.
- A `by_cases` whose proposition has an instance, such as `x = y` on
  `Name`, stays as it is.
- The `classical` lines stay while the toolchain lacks commit `541dbdcd`
  ([leanprover/lean4#15839](https://github.com/leanprover/lean4/pull/15839)).
  Once it has it, they may go.

## Why

Without an instance, `by_cases` relies on `Classical.propDecidable`, which
`open Classical` turns on through a process-wide list of scoped extensions.
`lean/` sets `doc.verso`, and in Lean v4.35.0 Verso elaborates each module
docstring with that list swapped for an empty one, on the main thread, while
proofs elaborate on other threads
([leanprover/lean4#15817](https://github.com/leanprover/lean4/issues/15817)).
A `by_cases` that runs during the swap fails with "failed to synthesize
Decidable p", at random, not on every build. It failed one Pages build of
`main` (#184). `classical` adds the instance as a local one, without the
list, so the outcome cannot depend on the race.

## Rejected alternatives

- **`rcases Classical.em p with h | h`.** It is safe too, but it names the
  goals `inl` and `inr`, and two proofs select the goal `neg`.
- **Turning `doc.verso` off.** The spec renders our docstrings as Verso.
