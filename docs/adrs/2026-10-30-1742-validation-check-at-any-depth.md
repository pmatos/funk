# `fir-ref` validates at any depth by replacing the spec's one walk of nested blocks

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
  `rfl`, so `fir-ref`'s calls of `Func.problems` and `Module.problems`
  reach them and never the spec's walk.
- **Tests.** `lean/FirTest/Validate.lean` checks modules with regions nested
  1,000,000 deep; without the `@[csimp]`, its build aborts with a stack
  overflow. A test of `fir-ref validate` on texts nested 10,000,000 deep is
  requested on #47 (comment 6529563279). It waits with #47, which is parked:
  no specific depth is an M0 acceptance bar (human ruling, 2026-10-30,
  comment 6530544151 on #47).

## Alternatives

- **Keep the spec's recursion in `fir-ref` and file the walk as a later
  stage.** The walk is small, so it lands with the check.
- **Write the spec's check with an explicit stack.** The spec would lose its
  readable definition of a function's blocks.

## Consequences

- A rule that reaches into regions, such as H6's scoping of values in
  regions, must take its blocks from the list that `Func.problemsIn` is
  given, or bring a loop of its own with a `@[csimp]` theorem.
- `fir-ref` decides validity with `Module.problems` or `Func.problems`,
  never with `decide`. The instances `Decidable m.Valid` and
  `Decidable (f.Valid ctx)` are compiled in the spec, before the `@[csimp]`
  theorems, so `decide` runs the spec's walk and takes stack per level of
  regions, even in code that imports `FirRef.Fast`. A `@[csimp]` theorem on
  the instance does not help, because the instance is inlined first; an
  instance of higher priority in `lean/FirRef/` would. #47 records it.
- Dominance takes one search of the function's graph per use whose
  definition is in another block, so `fir-ref validate` takes quadratic time
  in the worst case. ADR-2026-10-30-1450 asks for a replacement of that too;
  #55 tracks it, and waits with the other performance work.
- `fir-ref validate` on deeply nested texts is limited by the parser until
  #47 replaces its readers.
