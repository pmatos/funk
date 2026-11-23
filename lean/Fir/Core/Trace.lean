import Fir.Core.MemoryCallRefine
import Fir.Core.Event
import Fir.Core.Observe
import Fir.Execution.TraceRefine
import Fir.Execution.TraceDiverge
import Fir.Execution.TraceReplaceDiverge
import Fir.Execution.TraceLiftFrom

/-!
# The core's traced runs

The core's events are its external calls (`Fir.Core.Event`), which the world
answers with their results and its actions on escaped memory. Its traced
semantics runs each op by its rule with memory, lifted onto the memories of
the traced state: no op shows an event. An external call is not an op's
rule: the run hands a call to a declaration to the core's external-call
rule (`Fir.Execution.ExtCall`), which is to show the event (the human's
ruling of 2026-11-21 on #239, Q1). That rule is defined
(`Fir.Core.ExtCallRule`) but not yet installed: until #239's next stage
makes it the core's, the core's external-call rule is its rule with
memory, UB, lifted, so the core's traced semantics lifts its semantics
with memory, and its traced runs show no act, let nothing escape, and end
as its runs with memory, each return seen at its end
(`Fir.Execution.TraceLift`).

Two of the core's guarantees hold over its traced runs, the spec's, which
compare no addresses at the end of a return (`Func.observedRuns`), and at
every world, with no hypothesis beyond those they have with memory:

* _refined arguments_: on arguments that refine others, a poison by any
  value, the traced runs of every function of every core module refine its
  traced runs on those others, the end of each return included, calls and
  recursion included, wherever a run names the core's memories;
* _congruence in the callee_: replacing the body of a function `@g` of a
  valid core module with one under which `@g`, run in the new module from
  given memories, refines `@g` in the old, refines every function of the
  module over its traced runs, with no budget for the new `@g`: every core
  op has finitely many outcomes.

Its ops meet the obligation of the traced layer for a dialect that shows
events (`Fir.Execution.TraceObligations`): each runs by its rule with
memory, lifted, and is monotone with memory, and the lift onto the traced
state keeps it; its external-call rule, UB, is monotone too. They also meet
the hypothesis of that layer's divergence (`Fir.Execution.TraceFinite`):
each has finitely many outcomes with memory, so finitely many given the
world's answers, and an external call has one, UB.

So both are proved by the traced layer's own theorems for a dialect that
shows events: refined arguments by `Fir.Execution.TraceDiverge`, a proof
that stays once the core shows events and its traced semantics is no longer
this lift, and congruence in the callee by
`Fir.Execution.TraceReplaceDiverge`. Congruence in the callee keeps its
hypothesis with memory: since the core's traced semantics is the lift, a run
from a traced state ends as the run from its memories, so that hypothesis
gives the traced one (`Fir.Execution.TraceLiftFrom`). That step needs the
lift: once a run can make an external call, its traced semantics no longer
lifts its semantics with memory, and the bridge no longer applies; the
hypothesis is then over traced runs from every traced state (the human's
ruling of 2026-11-21 on #239, Q3).
-/

namespace Fir

/-- The core's traced semantics: its events are external calls, which the
world answers with their results and its actions on escaped memory, and
each op runs by its rule with memory, on the memories of the traced state,
showing no event. -/
instance Core.instDialectTrace : DialectTrace CoreDialect where
  Event := Core.Event
  Answer := Core.Reply × List WorldAct
  IsRefinedBy := Core.Event.IsRefinedBy
  traceAt lay ρ L :=
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    { denote op args := TraceM.liftMem (DialectDenote.denote op args)
      exit op args := TraceM.liftMem (DialectDenote.exit op args)
      extCall g args rs := TraceM.liftMem
        (DialectExtCall.extCall (m := StateT (Memory.Memories _ (unitsOf lay)) SetM) g args rs) }

/-- The core's traced semantics lifts its semantics with memory: no op shows
an event. -/
instance Core.liftsMem : LiftsMem CoreDialect :=
  ⟨fun lay ρ L => by
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    letI := DialectTrace.traceAt (d := CoreDialect) lay ρ L
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
   fun _ _ _ => fun _ _ _ => rfl⟩

/-- The world's default answer to a core event: no results and no actions. -/
instance Core.instInhabitedAnswer : Inhabited (DialectTrace.Answer CoreDialect) := ⟨([], [])⟩

namespace Core

variable {M : Module CoreDialect} {f : Func CoreDialect} {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N) (L : RunItems) (μ : Nat → N)

/-- Each core op runs, in the core's traced semantics, by its rule with
memory, lifted onto the memories of the traced state, wherever a run names
the core's memories: no op shows an event. -/
theorem opLiftsMem (op : Op) : OpLiftsMem (d := CoreDialect) lay ρ L op :=
  fun _ => ⟨rfl, rfl⟩

/-- Every core function's ops that run by their own rule are monotone in the
core's traced semantics, wherever a run names the core's memories: each
runs by its rule with memory, lifted, and is monotone with memory, and the
lift onto the traced state keeps it. -/
theorem traceOpsMonotone (g : Func CoreDialect) :
    letI := DialectTrace.traceAt (d := CoreDialect) lay ρ L
    g.TraceOpsMonotone (DialectTrace.Acts CoreDialect) (TraceState N (unitsOf lay)) :=
  Func.TraceOpsMonotone.ofLift lay ρ L (opLiftsMem lay ρ L) (fun _ _ _ => rfl)
    fun _ _ o _ hc => Op.memMonotone_all o.op hc lay ρ L

/-- Every core op that runs by its own rule has finitely many outcomes in
the core's traced semantics, given the world's answers, wherever a run names
the core's memories: each runs by its rule with memory, lifted, and has
finitely many outcomes with memory, and the lift onto the traced state
keeps it. -/
theorem opsTraceFinite :
    letI := DialectTrace.traceAt (d := CoreDialect) lay ρ L
    OpsTraceFinite CoreDialect (DialectTrace.Event CoreDialect) (DialectTrace.Answer CoreDialect)
      (TraceState N (unitsOf lay)) :=
  OpsTraceFinite.ofLift lay ρ L (opLiftsMem lay ρ L) (fun _ _ _ => rfl) (opsFinite lay ρ L)

/-- Refined arguments over traced runs: on arguments that refine others, a
poison by any value, the spec's traced runs of every function of every core
module refine its traced runs on those others, the end of each return
included, calls and recursion included, wherever a run names the core's
memories. It is proved by the traced layer's own theorem for a dialect
that shows events: the core's ops are monotone in the traced layer and have
finitely many outcomes given the world's answers. -/
theorem trace_args_isRefinedBy (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    traceObservable (f.observedRuns lay ρ L μ M a) ⊑
      traceObservable (f.observedRuns lay ρ L μ M a') :=
  Func.traceRuns_isRefinedBy_of_args lay ρ L μ _ Ty.isRefinedBy_trans (opsTraceFinite lay ρ L)
    (fun g _ => traceOpsMonotone lay ρ L g) (traceOpsMonotone lay ρ L f) h

/-- Refined arguments over traced runs, at every world: on arguments that
refine others, each outcome that the spec's traced runs of a function of a
core module show at a world on those others is allowed by an outcome of its
traced runs on the first, which shows the same answers. -/
theorem trace_args_isRefinedBy_world (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    ∀ w t, (traceObservable (f.observedRuns lay ρ L μ M a')).atWorld w t →
      ∃ s, traceObservable (f.observedRuns lay ρ L μ M a) s ∧ s ⊑ t :=
  TBehaviour.isRefinedBy_iff_world.1 (trace_args_isRefinedBy lay ρ L μ M f h)

/-- Congruence in the callee over traced runs: replacing the body of a
function `@g` of a valid core module with one under which `@g`, run in the
new module from given memories, refines `@g` in the old, refines every
function of the module over the spec's traced runs, calls and recursion
included, wherever a run names the core's memories. It asks for no budget,
whatever the parameter types of `@g` and whatever its new body does to the
memories: every core op has finitely many outcomes. It is proved by the
traced layer's own theorem for a dialect that shows events, its hypothesis
with memory taken to the traced one by the lift. -/
theorem trace_replaceBody_isRefinedBy_of_from (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (b : Region CoreDialect)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.observedRuns lay ρ L μ M ⊑
      (f.replaceBody g.name b).observedRuns lay ρ L μ (M.replaceBody g.name b) :=
  Func.traceRuns_replaceBody_isRefinedBy lay ρ L μ _ (opsTraceFinite lay ρ L)
    (fun g _ => traceOpsMonotone lay ρ L g) Ty.isRefinedBy_refl Ty.isRefinedBy_trans
    Event.isRefinedBy_trans hM.symbolsUnique hg b
    (fun p => Func.traceRunsFrom_isRefinedBy_of_memRunsFrom lay ρ L (h (p.1, p.2.mem))) hf

/-- Congruence in the callee over traced runs, at every world: under the
hypotheses of congruence in the callee from given memories, on every
argument vector, each outcome that the new function's traced runs show at a
world is allowed by an outcome of the old function's, which shows the same
answers. -/
theorem trace_replaceBody_isRefinedBy_of_from_world (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (b : Region CoreDialect)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    ∀ a w t, (traceObservable ((f.replaceBody g.name b).observedRuns lay ρ L μ
        (M.replaceBody g.name b) a)).atWorld w t →
      ∃ s, traceObservable (f.observedRuns lay ρ L μ M a) s ∧ s ⊑ t :=
  FuncTraceRuns.isRefinedBy_iff_world.1
    (trace_replaceBody_isRefinedBy_of_from lay ρ L μ hM hg b h hf)

end Core

end Fir
