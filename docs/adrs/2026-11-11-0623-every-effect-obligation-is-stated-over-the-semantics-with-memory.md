# Every effect obligation is stated over the semantics with memory, and a dialect that touches no memory ties its set-monad semantics to it

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-11-0451 states the memory-named effects' obligations over a
dialect's semantics with memory, `DialectMemDenote`. No may-UB and no may
produce poison were still stated over its semantics in the set monad, and
nothing tied the two semantics. An op that touches memory has no semantics
in the set monad, so those two obligations could say nothing of a load or
a store. And the runs with memory used any semantics in the state layer,
not the dialect's `DialectMemDenote`. Stage 2c-1 of
[#231](https://github.com/pmatos/funk/issues/231) settles both before the
first memory op lands (stage 4).

## Decision

- **No may-UB and no may produce poison speak of the semantics with
  memory.** `NeverUB` and `MakesNoPoison`
  ([`EffectLaws.lean`](../../lean/Fir/Execution/EffectLaws.lean)) hold
  wherever a run names the dialect's memories and from any memories, as the
  memory obligations do. `LawfulDialectEffects` no longer asks for a
  semantics in the set monad. The set-monad forms remain as
  `NeverUBSetM` and `MakesNoPoisonSetM`.
- **The tie is a class.** `LiftsSetM d`
  ([`MemoryRuns.lean`](../../lean/Fir/Execution/MemoryRuns.lean)) says
  that, at every naming, the semantics with memory is the set monad's,
  lifted into the state layer. `DialectMemDenote.ofSetM` meets it, and so do
  sums and lifts whose sides do. The core dialect and the test dialects
  meet it.
- **Theorems over runs in the set monad assume the tie.** Under it, an op
  meets each obligation in the set monad exactly when it meets it with
  memory (`NeverUB.setM`, `MakesNoPoison.setM`, and `.ofSetM` back). The
  soundness of function summaries (`Module.summary_neverUB`,
  `Module.summary_noPoison`) takes `LiftsSetM`.
- **Runs with memory run the dialect's semantics with memory.**
  `Func.memRuns unit ρ M f` runs `DialectMemDenote.denoteAt unit ρ`, from
  the empty memories. Under the tie, they are the runs in the set monad
  (`Func.memRuns_eq`).

This refines ADR-2026-11-11-0451 and ADR-2026-11-10-2350.

## Alternatives

- **A tie for every dialect, memory ops included.** A load has no
  meaning in the set monad, so the only ties would make it UB or give it no
  outcome there, and the runs in the set monad would then mean nothing for
  programs that touch memory.
- **Keep both obligations in the set monad and add the memory ones.** The
  class would ask a memory dialect for a set-monad semantics it cannot
  give.

## Consequences

- A dialect whose ops touch memory gives no `LiftsSetM`. Its no-UB and
  no-poison obligations hold over its semantics with memory, and theorems
  about its runs speak of its runs with memory.
- The summary theorems hold of dialects that lift the set monad. When the
  core dialect gains a memory op (stage 4 of #231), it no longer lifts the
  set monad, and the summary theorems need their statements over runs with
  memory before then.
- Runs with memory are fuel-monotone for every dialect, whatever its ops
  do to the memories (`Func.memRuns_fuelMonotone`). Progress and refinement
  with memory follow in stages 2c-2 and 2c-3 of #231.
