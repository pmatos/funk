import Fir.Core.MemoryCallRefine
import Fir.Core.Observe
import Fir.Execution.TraceRefine
import Fir.Execution.TraceDiverge
import Fir.Execution.TraceReplaceDiverge
import Fir.Execution.TraceLiftFrom

/-!
# The core's traced runs

The core shows no event yet: the tickets that bring external calls, volatile
accesses and inline assembly add its events. So its traced semantics is its
semantics with memory, lifted onto the memories of the traced state, and its
traced runs show no act, let nothing escape, and end as its runs with
memory, each return seen at its end (`Fir.Execution.TraceLift`).

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
events (`Fir.Execution.TraceObligations`): each is monotone with memory,
and the lift onto the traced state keeps it. They also meet the hypothesis
of that layer's divergence (`Fir.Execution.TraceFinite`): each has finitely
many outcomes with memory, so finitely many given the world's answers.

So both are proved by the traced layer's own theorems for a dialect that
shows events, as they stay once the core shows events and its traced
semantics is no longer this lift: refined arguments by
`Fir.Execution.TraceDiverge`, congruence in the callee by
`Fir.Execution.TraceReplaceDiverge`. Congruence in the callee keeps its
hypothesis with memory: since the core's traced semantics is the lift, a run
from a traced state ends as the run from its memories, so that hypothesis
gives the traced one (`Fir.Execution.TraceLiftFrom`). Neither proof uses
`LiftsMem`.
-/

namespace Fir

/-- The core's traced semantics: it shows no event, and each op runs by its
rule with memory, on the memories of the traced state. -/
instance Core.instDialectTrace : DialectTrace CoreDialect := DialectTrace.ofMem CoreDialect

/-- The core's traced semantics lifts its semantics with memory. -/
instance Core.liftsMem : LiftsMem CoreDialect := DialectTrace.ofMem_liftsMem CoreDialect

/-- The world's answers to the core's events: one, since it shows none. -/
instance Core.instInhabitedAnswer : Inhabited (DialectTrace.Answer CoreDialect) := ⟨()⟩

namespace Core

variable {M : Module CoreDialect} {f : Func CoreDialect} {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N) (L : RunItems) (μ : Nat → N)

/-- Every core function's ops that run by their own rule are monotone in the
core's traced semantics, wherever a run names the core's memories: each is
monotone with memory, and the lift onto the traced state keeps it. -/
theorem traceOpsMonotone (g : Func CoreDialect) :
    letI := DialectTrace.traceAt (d := CoreDialect) lay ρ L
    g.TraceOpsMonotone (DialectTrace.Acts CoreDialect) (TraceState N (unitsOf lay)) :=
  Func.TraceOpsMonotone.ofMem lay ρ L fun _ _ o _ hc => Op.memMonotone_all o.op hc lay ρ L

/-- Every core op that runs by its own rule has finitely many outcomes in
the core's traced semantics, given the world's answers, wherever a run names
the core's memories: each has finitely many with memory, and the lift onto
the traced state keeps it. -/
theorem opsTraceFinite :
    letI := DialectTrace.traceAt (d := CoreDialect) lay ρ L
    OpsTraceFinite CoreDialect (DialectTrace.Event CoreDialect) (DialectTrace.Answer CoreDialect)
      (TraceState N (unitsOf lay)) :=
  OpsTraceFinite.ofMem lay ρ L (opsFinite lay ρ L)

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
    (fun {e₁} => (e₁ : Empty).elim) hM.symbolsUnique hg b
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
