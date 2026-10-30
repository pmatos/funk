# fir functions and calls return any number of values, in M0 too

Status: accepted

## Context

The M0 epic ([#5](https://github.com/pmatos/funk/issues/5)), the roadmap and
S4 (ADR-2026-10-29-2008) speak of a function's "return value". The fir v0
spec's grammar lets functions and calls have any number of results, as MLIR
does, because one grammar serves every dialect (G0). The review of
[PR #29](https://github.com/pmatos/funk/pull/29) recommended limiting M0 core
functions and calls to at most one result. The human overrode that
recommendation on 2026-10-30 (choice 5 in the [rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304) on #5,
part 1).

## Decision

- Core functions, `ret` and `call` have any number of results in M0, none
  included. No validation rule limits them.
- What a returning run shows is the list of its returned values, each a
  value or poison. That list is M0's observation (`Core.Obs`), and
  refinement compares it value by value.
- `fir-ref`'s output, the harness's expected results and declared results
  are lists of values.

## Alternatives

- **At most one result in M0**, enforced by validation, with the grammar
  kept general. Rejected by the human.

## Consequences

- Where the epic, the roadmap and S4 say "return value", read "returned
  values". The orchestrator updates the epic and the roadmap; S4 stands, as
  its relation is already over a domain of observations.
- The x86-64 backend needs a convention for returning several values.
  System V returns at most two integer registers, so more results need
  memory, which M0 otherwise does not have. That takes a backend ticket of
  its own, and notes in #12 and #20.
- `fir-ref` and the differential harness (#10, #13) print and compare lists
  of values.
