# Refinement with memory refines memories unit by unit, from any memories, and asks each op to be monotone over the semantics with memory

Status: accepted
Tier: direction; area: semantics

## Context

The refinement theorems for runs with memory held only for a dialect that
lifts the set monad: its runs with memory are its runs in the set monad
(ADR-2026-11-11-0623). An op that touches memory has no semantics in the
set monad, so nothing said that its runs refine. Stage 2c-3 of
[#231](https://github.com/pmatos/funk/issues/231) gives runs with memory
their refinement before the first memory op lands (stage 4).

Facts that constrain it:

- A callee runs from the memories its caller reached, and its caller goes
  on from the memories the callee leaves. Runs with memory start from the
  empty memories and show only their returned values (#233).
- The human's rulings on #231 make a punned load give poison and keep
  provenance in a pointer's fragments. Stages 3 and 4 build on refinement.
- Call congruence in the set monad gets one fuel bound from finitely many
  argument vectors (ADR-2026-11-02-1426). The memories a call starts from
  are infinitely many. #214 owns congruence for infinitely many values.

## Decision

- **Memories refine unit by unit.** A poison unit is refined by any unit.
  A unit of bits or a pointer's fragment is refined only by itself. A block
  is refined by a block of the same kind, liveness and size; while it is
  live, the other's units refine its own one by one. No access reaches a
  freed block, so its units are not compared, and a store to a block that
  is then freed may be dropped. The memories of a run are refined by memories with
  the same frames and the same allocations, each memory refined block by
  block ([`Refine.lean`](../../lean/Fir/Memory/Refine.lean)). Entering and
  leaving a call, allocating, freeing, loading and storing keep it.
- **Monotonicity is stated over the semantics with memory.**
  `MemMonotone op`
  ([`MemoryOpRefine.lean`](../../lean/Fir/Execution/MemoryOpRefine.lean))
  holds when, at every naming and from memories that refine others, on
  operands that refine others, each way the op ends is allowed: UB, or
  results and memories that refine the source's. `LawfulDialectMonotone d`
  asks it of every valid op instance that is a terminator or has no
  callee. It is a class of its own, for the reasons ADR-2026-11-11-0801
  gives for totality. Under `LiftsSetM` it agrees with `OpMonotone`, and a
  lawful dialect meets it (`LawfulDialectMonotone.ofLawful`). Sums and
  lifts meet it when their sides do, with no tie.
- **Refinement compares runs from given memories.** `Func.memRunsFrom`
  runs a function from any memories and shows its returned values with the
  memories it ends with. Refined arguments and memories
  (`Func.memRunsFrom_args_isRefinedBy`) and congruence in the callee
  (`Func.memRunsFrom_replaceBody_isRefinedBy`) are stated over it. The
  runs with memory refine when these runs from the empty memories do
  (`Func.memRuns_isRefinedBy_of_from`).
- **A black box speaks of every memories.** Congruence assumes that the
  new `@g` refines the old from every memories, the end memories included.
  It assumes one fuel bound for the new `@g` from every memories, instead
  of finitely many argument vectors. #214 removes that assumption. For a
  dialect that lifts the set monad, `Func.memRuns_replaceBody_isRefinedBy_of_lawful`
  keeps the finiteness form.
- **The proofs stand beside those in the set monad.** As ADR-2026-11-11-0801
  chose for progress, `MemStepPath` and the path calculus of
  `StatePaths.lean` follow `RunPaths.lean`, `RefineUp.lean`,
  `RefineDown.lean`, `RefineRuns.lean` and `Replace.lean` step by step.
  `Func.memRuns_args_isRefinedBy_of_lawful` now needs no tie.

- **The relation on memories is a proof device, not the observation.**
  ADR-2026-11-09-1540 compares the end of a run by the memory reachable
  from globals and returned pointers, up to a one-to-one renaming of
  allocations, and rejects comparing all live memory, which would forbid
  removing dead stores. The relation here is stricter: the same allocations
  in the same order, every live unit compared. It is what a black box and
  congruence speak of, so that calls compose. What runs with memory show
  is still their returned values only (#233), so it adds no observation.
  It is the simplest relation that composes; a sound relation that does not
  compare everything a callee leaves needs the reachability and renaming
  that #233 defines. Until then, congruence does not cover a new callee that
  allocates differently, or drops a dead store to a block that stays live.
  When #233 lands, the hypotheses of these theorems are restated over its
  observation, and this decision is refined.

This refines ADR-2026-11-11-0801.

## Alternatives

- **Refine runs with memory only from the empty memories.** A callee runs
  from its caller's memories, so a black box stated so says nothing of a
  call, and congruence does not follow.
- **Let a unit of bits be refined by poison, or a fragment by bits.** A
  target could then lose a pointer's provenance or a stored value, which
  the source keeps.
- **Compare the units of freed blocks too.** No access reaches them, and a
  pass that drops a store to a stack slot just before its frame is left
  could not meet the black box's hypothesis.
- **Compare end memories as ADR-2026-11-09-1540 observes them now.** The
  reachable memory and the renaming of allocations are #233's to define;
  defining them here would decide that work ahead of it.
- **Derive the fuel bound here.** It needs König's lemma over the tree of
  choices, or another argument, which is #214's work.

## Consequences

- An op that touches memory proves `MemMonotone` with the laws that the
  memory model's operations keep refinement.
- Congruence with memory for a dialect whose ops touch memory needs the
  fuel bound until #214 lands.
- Congruence with memory does not yet cover a new callee whose end memory
  differs from the old one's outside what ADR-2026-11-09-1540 observes,
  such as a different allocation order, or a dead store to a live block.
  #233 restates it.
- Each change to `Func.runOps` is proved again in the memory refinement
  files, until the refactor that ADR-2026-11-11-0801 names.
