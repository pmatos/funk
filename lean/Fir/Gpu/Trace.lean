import Fir.Gpu.Runs
import Fir.Core.Trace
import Fir.Sum.Pointers
import Fir.Sum.Trace

/-!
# The traced runs of the core and `gpu`

`CoreGpu`'s traced semantics is the sum of the core's and `gpu`'s
(`Fir.Sum.Trace`), at every work-item: its events are the core's, the
external calls (`Fir.Core.Event`), since `gpu` shows none, and each op runs
by its side's traced rule. `gpu`'s is its semantics with memory, lifted
onto the memories of the traced state, and so is each core op's
(`Fir.Core.Trace`), so each op of the sum lifts its rule with memory: no
op shows an event, and the sum's traced semantics lifts its semantics with
memory. Its values hold the core's pointers, since `gpu` has no type of
its own (`Fir.Sum.Pointers`).

Two of its guarantees hold over the spec's traced runs (`Func.observedRuns`),
and at every world, with no hypothesis beyond those they have with memory:

* _refined arguments_: on arguments that refine others, the traced runs of
  every function of every module of the sum, a module of a nested table
  included, refine its traced runs on those others;
* _congruence in the callee_, from given memories, with no budget, for every
  callee of the module of each table of a valid module: every op of the
  sum has finitely many outcomes.

Its ops meet the obligation of the traced layer for a dialect that shows
events (`Fir.Execution.TraceObligations`), and the hypothesis of that
layer's divergence (`Fir.Execution.TraceFinite`), as the core's do. So
both are proved by the traced layer's own theorems
(`Fir.Execution.TraceDiverge`, `Fir.Execution.TraceReplaceDiverge`).
Congruence in the callee keeps its hypothesis with memory, which the lift
takes to the traced one (`Fir.Execution.TraceLiftFrom`), so that step
lasts only while no run of the sum can make an external call (#239).
-/

namespace Fir.Gpu

variable [WorkItem]

/-- The traced semantics of `gpu` over the core: it shows no event, and each
op runs by its rule with memory, on the memories of the traced state. -/
instance gpu_instDialectTrace : DialectTrace GpuDialect := DialectTrace.ofMem GpuDialect

/-- The traced semantics of `gpu` lifts its semantics with memory. -/
instance gpu_liftsMem : LiftsMem GpuDialect := DialectTrace.ofMem_liftsMem GpuDialect

/-- The traced semantics of the sum: the sum of the core's and `gpu`'s, which
shows the core's events. -/
instance coreGpu_instDialectTrace : DialectTrace CoreGpu := Dialect.sum.instDialectTrace

/-- The traced semantics of the sum lifts its semantics with memory: no op of
either side shows an event. -/
instance coreGpu_liftsMem : LiftsMem CoreGpu := Dialect.sum.liftsMem

/-- The world's default answer to an event of the sum: the core's. -/
instance coreGpu_instInhabitedAnswer : Inhabited (DialectTrace.Answer CoreGpu) := ⟨.inl default⟩

/-- Refinement of the sum's events is reflexive. -/
theorem event_isRefinedBy_refl : ∀ ev : DialectTrace.Event CoreGpu, ev ⊑ ev :=
  Dialect.sum.event_isRefinedBy_refl Core.Event.isRefinedBy_refl fun e => (e : Empty).elim

/-- Refinement of the sum's events is transitive. -/
theorem event_isRefinedBy_trans {e₁ e₂ e₃ : DialectTrace.Event CoreGpu} :
    e₁ ⊑ e₂ → e₂ ⊑ e₃ → e₁ ⊑ e₃ :=
  Dialect.sum.event_isRefinedBy_trans Core.Event.isRefinedBy_trans fun {e₁} => (e₁ : Empty).elim

variable {M : Module CoreGpu} {t : SymbolTable CoreGpu} {f : Func CoreGpu} {N : Type}
  [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreGpu → N) (L : RunItems)
  (μ : Nat → N)

/-- Each op of the sum runs, in its traced semantics, by its rule with memory,
lifted onto the memories of the traced state, wherever a run names the
sum's memories: each core op does in the core, and each op of `gpu` in
`gpu`. -/
theorem opLiftsMem : ∀ op, OpLiftsMem (d := CoreGpu) lay ρ L op :=
  Dialect.sum.opLiftsMem lay ρ L (fun o => Core.opLiftsMem lay _ L o)
    (OpLiftsMem.ofMem (d := GpuDialect) lay ρ L)

/-- Every function of the sum has its ops that run by their own rule
monotone in the sum's traced semantics, wherever a run names the sum's
memories: each runs by its rule with memory, lifted, and is monotone with
memory, and the lift onto the traced state keeps it. -/
theorem traceOpsMonotone (g : Func CoreGpu) :
    letI := DialectTrace.traceAt (d := CoreGpu) lay ρ L
    g.TraceOpsMonotone (DialectTrace.Acts CoreGpu) (TraceState N (unitsOf lay)) :=
  Func.TraceOpsMonotone.ofLift lay ρ L (opLiftsMem lay ρ L) (memOpsMonotone lay ρ L g)

/-- Every op of the sum that runs by its own rule has finitely many outcomes
in the sum's traced semantics, given the world's answers, wherever a run
names the sum's memories: each runs by its rule with memory, lifted, and
has finitely many outcomes with memory, and the lift onto the traced state
keeps it. -/
theorem opsTraceFinite :
    letI := DialectTrace.traceAt (d := CoreGpu) lay ρ L
    OpsTraceFinite CoreGpu (DialectTrace.Event CoreGpu) (DialectTrace.Answer CoreGpu)
      (TraceState N (unitsOf lay)) :=
  OpsTraceFinite.ofLift lay ρ L (opLiftsMem lay ρ L) (opsFinite lay ρ L)

/-- Refined arguments over traced runs: on arguments that refine others, the
spec's traced runs of every function of every module of the sum, a module
of a nested table included, refine its traced runs on those others, the end
of each return included, calls and recursion included, wherever a run names
the sum's memories. It is proved by the traced layer's own theorem for a
dialect that shows events: the sum's ops are monotone in the traced layer
and have finitely many outcomes given the world's answers. -/
theorem trace_args_isRefinedBy (M : Module CoreGpu) (f : Func CoreGpu)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    traceObservable (f.observedRuns lay ρ L μ M a) ⊑
      traceObservable (f.observedRuns lay ρ L μ M a') :=
  Func.traceRuns_isRefinedBy_of_args lay ρ L μ _ isRefinedBy_trans (opsTraceFinite lay ρ L)
    (fun g _ => traceOpsMonotone lay ρ L g) (traceOpsMonotone lay ρ L f) h

/-- Refined arguments over traced runs, at every world: on arguments that
refine others, each outcome that the spec's traced runs of a function of the
sum show at a world on those others is allowed by an outcome of its traced
runs on the first, which shows the same answers. -/
theorem trace_args_isRefinedBy_world (M : Module CoreGpu) (f : Func CoreGpu)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    ∀ w t, (traceObservable (f.observedRuns lay ρ L μ M a')).atWorld w t →
      ∃ s, traceObservable (f.observedRuns lay ρ L μ M a) s ∧ s ⊑ t :=
  TBehaviour.isRefinedBy_iff_world.1 (trace_args_isRefinedBy lay ρ L μ M f h)

/-- Congruence in the callee over traced runs: in the module of each table of
a valid module of the sum, replacing the body of a function `@g` with one
under which `@g`, run in the new module from given memories, refines `@g` in
the old, refines every function of the table over the spec's traced runs,
calls and recursion included, wherever a run names the sum's memories. It
asks for no budget, whatever the parameter types of `@g` and whatever its
new body does to the memories: every op of the sum has finitely many
outcomes. It is proved by the traced layer's own theorem for a dialect that
shows events, its hypothesis with memory taken to the traced one by the
lift. -/
theorem trace_replaceBody_isRefinedBy_of_from (hM : M.Valid) (ht : t ∈ M.tables)
    {g : Func CoreGpu} (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.observedRuns lay ρ L μ (M.nest t) ⊑
      (f.replaceBody g.name b).observedRuns lay ρ L μ ((M.nest t).replaceBody g.name b) :=
  Func.traceRuns_replaceBody_isRefinedBy lay ρ L μ _ (opsTraceFinite lay ρ L)
    (fun g _ => traceOpsMonotone lay ρ L g) isRefinedBy_refl isRefinedBy_trans
    event_isRefinedBy_trans (hM.nest ht).symbolsUnique hg b
    (fun p => Func.traceRunsFrom_isRefinedBy_of_memRunsFrom lay ρ L (h (p.1, p.2.mem))) hf

/-- Congruence in the callee over traced runs, at every world: under the
hypotheses of congruence in the callee from given memories, on every
argument vector, each outcome that the new function's traced runs show at a
world is allowed by an outcome of the old function's, which shows the same
answers. -/
theorem trace_replaceBody_isRefinedBy_of_from_world (hM : M.Valid) (ht : t ∈ M.tables)
    {g : Func CoreGpu} (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    ∀ a w t', (traceObservable ((f.replaceBody g.name b).observedRuns lay ρ L μ
        ((M.nest t).replaceBody g.name b) a)).atWorld w t' →
      ∃ s, traceObservable (f.observedRuns lay ρ L μ (M.nest t) a) s ∧ s ⊑ t' :=
  FuncTraceRuns.isRefinedBy_iff_world.1
    (trace_replaceBody_isRefinedBy_of_from lay ρ L μ hM ht hg b h hf)

end Fir.Gpu
