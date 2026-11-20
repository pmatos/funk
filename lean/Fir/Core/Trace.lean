import Fir.Core.MemoryCallRefine
import Fir.Core.Observe
import Fir.Execution.TraceRefine

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

Once the core shows events, its traced semantics is no longer this lift,
and these theorems are proved by the theorems of the traced layer (stages
3b and 3c of #233), with the same statements.
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

/-- Refined arguments over traced runs: on arguments that refine others, a
poison by any value, the spec's traced runs of every function of every core
module refine its traced runs on those others, the end of each return
included, calls and recursion included, wherever a run names the core's
memories. -/
theorem trace_args_isRefinedBy (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    traceObservable (f.observedRuns lay ρ L μ M a) ⊑
      traceObservable (f.observedRuns lay ρ L μ M a') :=
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
  have hm : ∀ g : Func CoreDialect, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => Op.memMonotone_all o.op hc lay ρ L
  Func.traceRuns_isRefinedBy_of_from lay ρ L μ _ Ty.isRefinedBy_trans
    (Func.memRunsFrom_args_isRefinedBy M (fun g _ => hm g) f (hm f) h
      (Memory.Memories.isRefinedBy_refl _))

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
memories: every core op has finitely many outcomes. -/
theorem trace_replaceBody_isRefinedBy_of_from (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (b : Region CoreDialect)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.observedRuns lay ρ L μ M ⊑
      (f.replaceBody g.name b).observedRuns lay ρ L μ (M.replaceBody g.name b) :=
  Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ L μ _ Ty.isRefinedBy_refl
    Ty.isRefinedBy_trans (opsFinite lay ρ L) hM hg b h hf

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
