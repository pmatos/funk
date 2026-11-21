# Current decisions: semantics, refinement over M1 traced runs

This page continues semantics-m1-trace.md, which says what an M1 run shows.
It says how the refinement theorems, refined arguments and congruence in
the callee, hold over traced runs. It is the record: when this page and an
ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). ADR-2026-11-09-1540 holds the direction decision.

These are decided designs. The spec states the core's and CoreGpu's traced
runs, with refined arguments and congruence in the callee over them while
they show no event (`lean/Fir/Execution/TraceLift.lean`,
`TraceRefine.lean`, `lean/Fir/Core/Trace.lean`, `lean/Fir/Gpu/Trace.lean`).
For a dialect that shows events, the spec defines the obligation of its
ops and proves that refined arguments allow each return, each UB and each
path out of fuel at its budget (`lean/Fir/Execution/TraceObligations.lean`
to `TraceArgs.lean`), and, when its ops have finitely many outcomes given
the world's answers, divergence too, so refined arguments in full
(`TraceSteps.lean` to `TraceDiverge.lean`); the core and CoreGpu prove
theirs that way. For congruence in the callee over the traced runs of such
a dialect, the spec proves that replacing a callee's body by one that
refines it makes the new module run each call as the old one does, and
that each return and each UB of a caller in a module that does is allowed
by the old (`TraceAhead.lean` to `TraceReplace.lean`). Divergence across the replaced callee is not
implemented yet (#233, stage 3c-2), nor are the core's and CoreGpu's
congruence in the callee through that engine.

## Refinement over traced runs

These are #233's choices of form for its third stage, within the rules of
semantics-m1-trace.md.

- **A dialect with no event.** Its traced semantics is its semantics with
  memory, lifted onto the memories of the traced state
  (`DialectTrace.ofMem`), so it lifts it (`LiftsMem`) by construction. The
  core and CoreGpu have this traced semantics until their events exist.
  Rejected: a traced semantics written op by op for the core now, which
  #239 would rewrite once the core shows its first event.
- **From memory to the end of a return.** Returned values that refine
  others and memories that refine others, with the same allocations
  escaped, give ends of returns that refine each other under the renaming
  of every allocation to itself (`End.isRefinedBy_of_mem`). So, for a
  dialect with no event, refinement from the empty memories, the memories
  each run ends with included, gives refinement of its traced runs
  (`Func.traceRuns_isRefinedBy_of_from`), and refined arguments and
  congruence in the callee from given memories hold over its traced runs
  and at every world (`Fir.Execution.TraceRefine`). The core and CoreGpu
  state both over the spec's traced runs (`Func.observedRuns`), with no
  hypothesis beyond those they have with memory. Rejected: keep the core's
  guarantees over its runs with memory alone until the traced layer's own
  theorems exist, so the spec's traced runs would have none meanwhile.
- **A dialect with events.** Its refined arguments and congruence in the
  callee are the traced layer's own theorems (#233, stages 3b and 3c),
  which are to prove the core's statements again, unchanged, once the core
  shows events. Divergence needs one source trace at every budget. An op with
  infinitely many outcomes `c` can show, on a poison argument, an event
  that differs with each `c` and is refined by the target's, then take `c`
  silent steps and return. The target then falls silent after its event,
  and no source outcome allows it. So the generic theorems of stages 3b
  and 3c take a hypothesis: each op has finitely many outcomes given the
  world's answers, as congruence with memory takes `OpsFinite`. The core's
  and CoreGpu's statements take no hypothesis: both meet it
  (`Core.opsTraceFinite`, `Gpu.opsTraceFinite`). The human ruled this on
  2026-11-20, on #233. Rejected: change how stage 1 judges divergence
  (`traceObservable`), a definition already merged.
- **The hypothesis, by position.** An op has finitely many outcomes given
  the world's answers (`OpsTraceFinite`) when, from each traced state and
  for each answer stream, its results whose acts agree with the stream
  place by place lie in one finite list: the agents' reading of the
  ruling. Rejected: finitely many for each list of answers, which an op
  showing `k` events for every `k` meets; then, on paper (not in Lean), a
  target could show acts forever that no source run shows.
- **Divergence by König's lemma.** A call shows no step, so the fuel
  between two steps is bounded by the module's chains of calls into entry
  blocks (`Module.exists_callBound`); a cycle never shows a step again
  (`Func.traceOps_silent`). A path cut at a budget `W (N + 1)` keeps its
  first `N` steps (`Func.traceOps_cut`, `Func.traceRuns_truncates`). With finitely many traces at one budget, the
  pigeonhole principle and König's lemma give the source's trace
  (`TRun.diverge_allowed`, `TRun.reacts_allowed`). Rejected: a hypothesis
  bounding that fuel, which every core module needs.
- **The obligation of an op with events.** An op is monotone in the traced
  layer (`OpTraceMonotone`): from operands and a traced state that refine
  others, each way it may end is allowed by a way it may end on those
  others. One traced state refines another when its memories refine the
  other's and the same allocations escaped, in the same order, so the
  world names each by the same handle. A result allows a result that
  refines it, after acts that refine its own one by one, with a traced
  state that refines its own. UB after the acts `t` allows any way of
  ending that first shows acts refining `t`. The step before each op and
  the lift of a semantics with memory keep the obligation, so the core and
  CoreGpu meet it from their monotonicity with memory
  (`Core.traceOpsMonotone`, `Gpu.traceOpsMonotone`). Rejected: escaped
  lists related only by the renaming of allocations, which refined
  arguments do not need: both runs allocate the same ids, in step.
- **Refined arguments run in step.** On arguments that refine others, a
  function's traced runs and its runs on those others run the same ops at
  the same budget, with the same steps left after each return. So each
  path of the first that is not stuck is allowed by a path of the second
  at the same budget (`Func.traceRun_allowed`). Each return and each UB
  of the traced runs is allowed, and so is each path out of fuel, at its
  budget (`Fir.Execution.TraceArgs`). Rejected: allow a path by one at a
  smaller budget, as the theorems with memory do for black boxes, which
  only congruence in the callee needs (stage 3c).

## Congruence in the callee over traced runs

These are #233's choices of form for stage 3c, within the rules of
semantics-m1-trace.md.

- **Runs from a traced state.** A callee runs from the traced state its
  caller reached, and its caller goes on from the one it leaves. So the
  hypothesis compares the new callee with the old one on their traced runs
  from every traced state, which return their values with the traced state
  they end in (`Func.traceRunsFrom`), as congruence with memory compares runs
  from every memories. Rejected: compare them only from the empty memories,
  which says nothing of a call made from another traced state.
- **A traced black box.** Each call of the replaced callee is a black box:
  on arguments and traced states that refine others, the new callee's traced
  behaviour, the traced states it ends in included, refines the old one's
  (`TraceBlackBox`). Replacing a body gives one from the hypothesis and
  refined arguments from a traced state (`Func.traceRunsFrom_isRefinedBy_of_args`,
  divergence included), when refinement of values and of events is
  transitive (`Module.replaceBody_traceCallsRefined`). Rejected: ask the
  black box of the generic theorem directly, which leaves every caller to
  prove refined arguments from a traced state.
- **Allowed at some budget, acts compared.** The old callee and the new one
  may take different numbers of steps, so a caller's two runs do not go in
  step. A path of the new module's run is allowed by one of the old module's
  at some budget, comparing acts, not steps (`TAllowed`), as the theorems
  with memory allow a black box's path at some budget
  (`Fir.Execution.MemoryBlackBox`). More fuel keeps a return, with as many
  more steps left, and UB (`Func.traceOps_up`), so a callee's return at one
  budget and the rest's at another give the whole's at their sum plus one.
  Rejected: allow in step, as refined arguments do, which a replaced body
  with a different number of steps breaks.
- **Divergence across the callee.** It is stage 3c-2 of #233. In-step
  divergence (`TRun.ExhaustedAllowed`) compares the two runs tick for tick
  at each budget, and a black box speaks only of behaviours, never of one
  path out of fuel, so it needs an argument of its own, under the ruled
  hypothesis that each op has finitely many outcomes given the world's
  answers. Rejected: reuse in-step divergence across the black box, which
  a replaced body that takes a different number of steps breaks.
