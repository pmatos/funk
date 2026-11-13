# Current decisions: semantics, refinement

This page continues semantics.md. It says what holds today about what
correctness means and the theorems that compose it. It is the record: when this
page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). ADR-2026-10-29-2008 and ADR-2026-11-09-1322 hold the
direction decisions, and ADR-2026-11-09-1541 the monotonicity obligation with
memory. semantics-m1-trace.md says what an M1 run shows.

## Refinement

A target is correct if each of its observable behaviours is allowed by the
source. Source UB allows any target that first shows the source's events before
the UB (ADR-2026-11-09-1540). A poison result is refined by any value.
Refinement is defined over a domain of observations that the semantics supplies.
Each dialect supplies its observations (ADR-2026-10-29-2008). This is S4, agreed
with the human on 2026-10-29 (#5). Rejected: asking the target to behave as the
source does, which leaves it no freedom where the source has UB or poison.

Core functions, `ret` and `call` have any number of results, none included. No
validation rule limits them. What a returning run shows is the list of its
returned values, each a value or poison. That list is M0's observation
(`Core.Obs`), and refinement compares it value by value. `fir-ref`'s output,
the harness's expected results and declared results are lists of values
(ADR-2026-10-29-2008). The human ruled this on 2026-10-30, overriding the
review of PR #29 (choice 5 of the rulings comment on #5). Rejected: at most one
result in M0, enforced by validation with the grammar kept general. Where an
older text says "return value", read "returned values".

In M0, a function's observable behaviour is its returned values, UB, or
non-termination (fuel exhausted). The full definition also counts calls to
external symbols and reachable memory. M0 has no memory, and every M0 callee is
inside the module. The one exception is the `i128` division helper, which is
tested on its own. M1 makes observable behaviour a trace judged for each world
(ADR-2026-11-09-1540). The relation stays the same (ADR-2026-10-29-2008).

The differential harness compares a native result with the `fir-ref` result by
refinement. A poison result from `fir-ref` matches any native value. A test
whose `fir-ref` result is UB is invalid, never a pass. `freeze` makes the
source's behaviour a set of outcomes, and ADR-2026-10-29-2017 says how the
harness checks a native result against that set. Any later check, such as
per-compile refinement checking (S8, not decided), checks this relation and no
other (ADR-2026-10-29-2008).

Monotonicity makes refinement compositional. Replacing one part of a function
with a part that refines it refines the whole function (ADR-2026-10-29-2006).

## Behaviour models

The core dialect's behaviour is a set of outcomes. Its refinement is set
refinement: each outcome of the target is allowed by some outcome of the
source (`Behaviour.IsRefinedBy`). The theorems about behaviour and refinement in
`lean/Fir` are about this set instance (ADR-2026-11-09-1322).

The seam for other behaviour models has two parts. The interpreter is generic
over its monad: `Func.run` takes any monad `m` with `DialectDenote d m`. The
tree of choices maps to a meaning by a monad morphism. `Func.run_map` carries
any such morphism to the interpreter's run (ADR-2026-11-09-1322).

A dialect that needs probabilistic behaviour supplies its own model. A model is
an interpretation of the tree, or of the tree extended with the dialect's own
effect, as a `MonadMorphism`. It comes with a refinement order on that model.
On the outcomes a model gives with non-zero weight, its order must imply set
refinement. So results proved for the set instance stay valid as statements
about which outcomes are possible. They say nothing about how likely an outcome
is (ADR-2026-11-09-1322).

A behaviour-model class with `SetM` as one instance is deferred. It waits for a
real probabilistic dialect to give a second instance to design against, and
that dialect restates the generic results it needs. Passing
set refinement does not show that a target keeps a distribution: the dialect's
own order has to catch that. `lean/FirTest/G0.lean` tests the seam with a toy
tree of weighted choices, `WeightedTree`, mapped to a finite distribution
through a `MonadMorphism`; if the interpreter stops being generic over its
monad, it stops building (ADR-2026-11-09-1322). The human ruled this on
2026-11-09 (#166): name the seam now, and generalize later. Rejected: a
behaviour monad that the dialect set supplies now, with `SetM` as M0's
instance, which would restate the generic results before a second instance
exists to check the design.

## The ops a run reaches

The refinement engine asks monotonicity only of the ops a run can reach. Those
are the ops of the source module's functions and of the function that runs:
`Func.OpsMonotone f` says that every terminator and every op with no callee of
`f` is monotone. `Func.runs_isRefinedBy_of_calls`, `Func.runs_args_isRefinedBy`
and `Func.runs_replaceBody_isRefinedBy` take it over the source module, and the
first two take it for the function that runs. `Func.Valid.opsMonotone` gives it
for a valid function from monotonicity at valid op instances alone, in
`lean/Fir/Execution/Lawful.lean`. So a lawful dialect gets both function-level
refinement theorems for valid modules from the class alone, as the test dialect
`CoreProbe` does in `lean/FirTest/LawfulRefine.lean`. `Core.args_isRefinedBy`,
now over runs with memory, and `Core.replaceBody_isRefinedBy` keep their
hypotheses through `Core.opsMonotone_all`: every core function's ops are
monotone, valid or not. So `Core.args_isRefinedBy` holds for every function of
every core module, valid or not. The human ruled on 2026-11-05 (#99) to do this before M1 adds memory.
Rejected: asking monotonicity at valid op instances in the engine, with a valid
module, since `Core.args_isRefinedBy` could not then keep its statement; and
threading `Func.InModule`, which progress needs but refinement does not, since
it treats a stuck path as allowed.

## Congruence in the callee

Replacing a callee is replacing a body. `M.replaceBody s b` is the module `M`
with the region `b` in place of the body of its function `@s`. Every function
keeps its symbol, its parameters and its result types, so the runs of the old
and the new function have one type and need no cast. Congruence assumes that the
new `@g`, run in the new module, refines the old `@g`, run in the old. It
concludes the same relation for every function of the module
(`Core.caller_isRefinedBy`, `Core.replaceBody_isRefinedBy`, which ask that the
module be valid and that `@g` have no pointer parameter). It needs nothing of
the new body, because a call of `@g` is a black box whose behaviour the
hypothesis gives. When the new body calls back into the module, proving the
hypothesis may need its own induction. A body that gets stuck at once meets the
hypothesis with an empty behaviour, so the comparison is between real behaviours
when the new function is valid in the old module's context
(`Module.valid_replaceBody`). Rejected: the new callee run in the old module,
which is false: if `@g` returns `0`, the body `call @g` refines it in the old
module, but in the new one it calls itself and never returns.

`Func.runs_replaceBody_isRefinedBy` asks that the parameter types of `@g` have
finitely many argument vectors. Then one budget bounds every run of the new
`@g` that does not diverge (`exists_common_bound`): each argument vector has its
own budget, and without a bound on how many there are, a caller whose
arguments grow without limit could make the new `@g` run ever longer.
`Core.argVectors` lists the core's vectors. A dialect with a type of infinitely
many values cannot use the general theorem as it is. Refined arguments need no
finiteness, since they replace no callee. `ptr` has values now, infinitely
many, so the core's congruence is restated for a callee with no pointer
parameter, and #214 proves it for the rest (ADR-2026-11-09-1542). Rejected:
König's lemma over the tree of choices, which needs an infinite path through
runs at every budget that the spec does not have.

## Refinement with memory

Runs with memory refine too, whatever their ops do to the memories. A poison
unit of memory is refined by any unit, and a unit of bits or a pointer's
fragment only by itself. A block is refined by a block of the same kind,
liveness and size, whose units refine its own one by one while it is live.
No access reaches a freed block, so its units are not compared, and a store to
a block that is then freed may be dropped. Refined memories have the same
frames and allocations, each memory refined block by block
(`lean/Fir/Memory/Refine.lean`). Entering and leaving a call, allocating,
freeing, loading and storing keep it. The human ruled on #231 on 2026-11-11
that a punned load gives poison and that a pointer's fragments keep its
provenance, and this order builds on both. Rejected: letting poison refine a
unit of bits, or bits a fragment, so that a target could lose a stored value or
a pointer's provenance that the source keeps.

A dialect lawful in its monotonicity (`LawfulDialectMonotone`) has each valid
terminator and each valid op with no callee monotone over its semantics with
memory, at every naming and from memories that refine others (`MemMonotone`;
ADR-2026-11-09-1541). It is a class of its own, as `LawfulDialectTotal` is
(semantics-interpreter.md). A dialect that lifts the set monad and is lawful
meets it, and so do sums and lifts whose sides do. An op that touches memory
proves `MemMonotone` with the laws by which the memory model's operations keep
refinement.

Refinement then compares runs from given memories, the end memories included,
since a callee runs from its caller's memories (`Func.memRunsFrom`). Refined
arguments and memories need nothing more
(`Func.memRunsFrom_args_isRefinedBy`), and congruence is
`Func.memRunsFrom_replaceBody_isRefinedBy`. The runs with memory refine when
these runs from the empty memories do. Congruence assumes that the new callee
refines the old from every memories, and one fuel bound for it in place of
finitely many argument vectors, until #214. For a dialect that lifts the set
monad, the finiteness form stays. The core's congruence with memory is
`Core.memReplaceBody_isRefinedBy`, with the bound; its finiteness form,
`Core.replaceBody_isRefinedBy`, stays over the runs in the set monad until the
human rules whether it may go before #214 (the 4b-3 split on #231). These proofs stand beside those in the set
monad, step by step, and each change to `Func.runOps` is proved again in the
memory refinement files until the refactor that semantics-interpreter.md names.
Rejected: refining runs with memory only from the empty memories, since a black
box stated so says nothing of a call.

The relation on end memories is a proof device for composing calls, not an
observation. It is stricter than the observation of ADR-2026-11-09-1540: the
same allocations in the same order, every live unit compared. What runs with
memory show is still their returned values only. So congruence does not yet
cover a new callee that allocates in another order or drops a dead store to a
block that stays live. #233 defines the reachable memory and the renaming of
allocations, and then these hypotheses are restated over its observation.
Rejected: comparing end memories as ADR-2026-11-09-1540 observes them now,
which would decide #233's work ahead of it.
