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
now over runs with memory, keeps its hypotheses through each core op's own
monotonicity (`Core.Op.monotone_all`, tied into `Core.Op.memMonotone_all`):
every core function's ops are monotone, valid or not. So `Core.args_isRefinedBy`
holds for every function of every core module, valid or not. Congruence in the
callee with memory goes through the lawful class (`LawfulDialectMonotone`), so
the core's congruence asks for a valid module, as it did before. The human ruled on 2026-11-05 (#99) to do this before M1 adds memory.
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
(`Core.replaceBody_isRefinedBy_of_from`, over runs from given memories,
which asks only that the module be valid; and `Core.caller_isRefinedBy`,
`Core.replaceBody_isRefinedBy`, whose hypothesis is refinement with memory,
which also ask that `@g` have no pointer parameter and reach no memory; see
refinement with memory below). It needs nothing of
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
many values cannot use that theorem as it is, and with memory neither can any
dialect: a call starts from its caller's memories, which are infinitely many,
so finitely many argument vectors bound only a callee that touches no memory
(below). `ptr` has values now, infinitely many (ADR-2026-11-09-1542).

For runs with memory, König's lemma over the tree of choices removes the
condition (#214). Reading divergence as running out of fuel at every budget
already assumes that every choice has finitely many options
(`lean/Fir/Execution/Behaviour.lean`). With memory that is a hypothesis of
the theorems, `OpsFinite`: every op that runs by its own rule has finitely
many outcomes, its results or where control goes, with the memories it ends
with. Then a run at one budget returns finitely many things, and a source
that never hits UB and does not run out of fuel at a budget _N_ bounds its
target: by induction on _N_, each op and each call's returns go on in
finitely many ways, each with its own budget, and the largest serves. A
black box's target cannot diverge on an input where its source does not, so
it has a budget for that input. So congruence with memory asks for no
budget for the new callee, whatever its parameter types and whatever it does
to the memories (`Func.memRunsFrom_replaceBody_isRefinedBy_of_opsFinite`, in
`lean/Fir/Execution/MemoryFiniteReplace.lean`, from the engine
`Func.memOps_notExhausted_of_finite`, in
`lean/Fir/Execution/MemoryFiniteDown.lean`). The argument is by budgets and
needs no infinite path. Every core op has finitely many outcomes
(`Core.opsFinite`): it is the set of its rule in the tree of choices, whose
choices of _w_ bits have 2 to the power _w_ options. So
`Core.replaceBody_isRefinedBy_of_from` holds for every core callee,
pointers and memory included. No core op touches memory yet; one that does,
such as an allocation, will have to show the hypothesis by its own rule.
Nothing asks that every core function reach no memory. The hypothesis is passed to the theorems, as
`OpsIgnoreMemory` is, not added to a lawful class, so no dialect's
obligations change. Refined arguments need no finiteness, since they
replace no callee, and keep the engine with a bound of zero. Rejected: an
infinite path through the runs at every budget, which the spec does not
have; and a fuel bound asked of each new callee, which made each pass that
replaces a callee prove one.

## Refinement with memory

Runs with memory refine too, whatever their ops do to the memories. A poison
unit of memory is refined by any unit, and a unit of bits or a pointer's
fragment only by itself. A block is refined by a block of the same kind,
alignment, liveness and size, whose units refine its own one by one while it
is live. So an access that stage 4e of #231 checks against an allocation's
alignment is aligned in both runs or in neither. A pass that raises an
alignment is not covered yet, as with the other limits of this proof device
below.
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
refines the old from every memories, and either one fuel bound for it in
place of finitely many argument vectors
(`Func.memRunsFrom_replaceBody_isRefinedBy`), or that the dialect's ops have
finitely many outcomes, with no bound (congruence in the callee, above). For
a dialect that lifts the set monad, the finiteness form holds through its
runs in the set monad (`Func.memRuns_replaceBody_isRefinedBy_of_lawful`).

A callee whose effects include no memory read, write or allocation needs no
bound: its runs do not depend on the memories, so finitely many argument vectors
give it, as for runs in the set monad. Such a callee reaches no memory in the
new module (`SymbolTable.ReachesNoMemory`): no function that its run may reach
declares a memory effect. That follows from its summary touching none
(`Effects.TouchesNoMemory`, `SymbolTable.ReachesNoMemory.of_summary`), but a
call to a symbol the module does not define, which adds every effect to a
summary, adds nothing here, since a run is stuck there; so a new body with
such a call, which the form over the runs in the set monad covered, is still
covered. The dialect's ops that declare no memory effect must ignore the
memories (`OpsIgnoreMemory`): from any memories they end the same way and keep
them, which the effect obligations alone do not give. Then every run of a
function that reaches no memory ignores the memories,
calls and recursion included (`Module.memOps_ignoresMemory`), and its runs from
given memories are bounded (`Func.memRunsFrom_boundedBy_of_finite`), in
`lean/Fir/Execution/MemoryFreeRuns.lean`. Congruence is then
`Func.memRuns_replaceBody_isRefinedBy_of_finite`, and, when the old callee
reaches no memory too, `Func.memRuns_replaceBody_isRefinedBy_of_memRuns`,
whose hypothesis is refinement with memory, as it was over the runs in the set
monad. The core's congruence with memory takes this form:
`Core.replaceBody_isRefinedBy` and `Core.caller_isRefinedBy`, in
`lean/Fir/Core/MemoryCallRefine.lean`. No core op declares a memory effect, so
every core function reaches no memory (`Core.reachesNoMemory`), and these
forms hold of every core callee with no pointer parameter, as the forms over
the runs in the set monad did. A callee that touches memory used the form
with the bound, `Core.memReplaceBody_isRefinedBy`, until #214. Since #214,
the form from given memories, `Core.replaceBody_isRefinedBy_of_from` and
`Core.caller_isRefinedBy_of_from`, asks for no bound, no pointer-free
parameters and no callee that reaches no memory (congruence in the callee,
above), so the bound form is no longer needed. The forms over the runs in the
set monad and `Core.liftsSetM` went, so a memory op can join the core. The
human ruled this on 2026-11-13 (#373, option C). Rejected: (A) the bound form for every callee until #214, which would have
made each optimizer pass prove a bound for the callee it replaces, a weaker
theorem than the one that held for callees with no pointer parameter; (B) #214
before stage 4d, which would have held every memory op back for it.

These proofs stand beside those in the set
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
