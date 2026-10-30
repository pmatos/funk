# The validation check walks nested blocks once, and `fir-ref` runs a walk with no stack per level

Status: accepted

## Context

fir has no nesting limit (ADR-2026-10-30-1549): `fir-ref validate` must give
its verdict on a module nested to any depth. The spec's validation rules
reach into the regions of ops in one place, `Func.allBlocks`, a mutual
recursion that takes stack per level of regions and per block of a list.
Items cannot nest in M0, and a core op's attributes are decoded into a flat
op instance, so regions are the only nesting that validation walks.
ADR-2026-10-30-1450 gives the way `fir-ref` runs a loop proved equal to a
spec function.

## Decision

- **The spec's check walks nested blocks once.** `Func.problems` calls
  `Func.allBlocks` and passes the list to `Func.problemsIn`, which reads no
  other nested part of a function and walks lists only, in loops that are
  tail calls or core's tail-recursive list functions.
- **`fir-ref` replaces that walk.** `FirRef.allBlocks`
  (`lean/FirRef/Validate.lean`) lists the same blocks with an explicit
  stack of frames. `allBlocks_eq_allBlocks : @Func.allBlocks =
  @FirRef.allBlocks` is registered with `@[csimp]`. `FirRef.funcProblems`
  and `FirRef.moduleProblems` are copies of `Func.problems` and
  `Module.problems`, compiled after it and registered with `@[csimp]` by
  `rfl`, so `fir-ref` calls them and never the spec's walk.
- **Tests.** `lean/FirTest/Validate.lean` checks modules with regions nested
  1,000,000 deep; without the `@[csimp]`, its build aborts with a stack
  overflow. A test of `fir-ref validate` on texts nested 10,000,000 deep
  joins #47's acceptance checks, once `fir-ref` reads such texts.

## Alternatives

- **Keep the spec's recursion in `fir-ref` and file the walk as a later
  stage.** The walk is small, so it lands with the check.
- **Write the spec's check with an explicit stack.** The spec would lose its
  readable definition of a function's blocks.

## Consequences

- A rule that reaches into regions, such as H6's scoping of values in
  regions, must take its blocks from the list that `Func.problemsIn` is
  given, or bring a loop of its own with a `@[csimp]` theorem.
- `fir-ref validate` on deeply nested texts is limited by the parser until
  #47 replaces its readers.
