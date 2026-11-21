import Fir.Execution.TraceLift
import Fir.Execution.MemoryFiniteReplace

/-!
# Refinement over the traced runs of a dialect with no event

For a dialect whose ops show no event, the two refinement theorems for whole
functions hold over its traced runs, from the theorems with memory
(`Fir.Execution.TraceLift`):

* _refined arguments_: in a module whose functions are valid, a function's
  traced runs on arguments that refine others, a poison by any value,
  refine its traced runs on those others, the end of each return included;
* _congruence in the callee_: in a valid module, replacing the body of its
  function `@g` with one under which `@g`, run in the new module from given
  memories, refines `@g` in the old, refines every function of the module
  over its traced runs, with a budget for the new callee or, when the
  dialect's ops have finitely many outcomes, with none.

They hold at every world (`FuncTraceRuns.isRefinedBy_iff_world`): a dialect
whose ops show no event shows no act, so each world sees the same outcomes.
A dialect whose ops show events needs the theorems of the traced layer
itself, which stages 3b and 3c of #233 give.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] [DialectValidation d] [TyRefinement d.Ty]
  [TyPointers d.Ty] [LawfulDialectMonotone d] [DialectTrace d] [LiftsMem d] {N : Type}
  [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
  (μ : Nat → N) (ar : AddrRule) {ctx : ModuleContext d} {M : Module d}

/-- Refined arguments over traced runs, by the class alone, for a dialect
whose ops show no event: in a module whose functions are all valid, a
function's traced runs on arguments that refine others, a poison by any
value, refine its traced runs on those others, wherever a run names the
dialect's memories, calls and recursion included, when the refinement of
values is transitive. -/
theorem Func.traceRuns_args_isRefinedBy_of_lawful
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func d} (hf : f ∈ M.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑
      traceObservable (f.traceRuns lay ρ L μ ar M a') :=
  Func.traceRuns_isRefinedBy_of_from lay ρ L μ ar htrans
    (Func.memRunsFrom_args_isRefinedBy_of_lawful lay ρ L hv hf ha (Memories.isRefinedBy_refl _))

/-- Congruence in the callee over traced runs, by the class alone, for a
dialect whose ops show no event: in a valid module, replacing the body of
its function `@g` with one under which `@g`, run in the new module from
given memories, refines `@g` in the old, refines every function of the
module over its traced runs, wherever a run names the dialect's memories,
calls and recursion included, whatever the new body. It asks what
congruence with memory asks, the budget for the new `@g` included. -/
theorem Func.traceRuns_replaceBody_isRefinedBy_of_bound
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hbound : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.traceRuns lay ρ L μ ar M ⊑
      (f.replaceBody g.name b).traceRuns lay ρ L μ ar (M.replaceBody g.name b) := fun a =>
  Func.traceRuns_isRefinedBy_of_from lay ρ L μ ar htrans
    ((Func.memRuns_replaceBody_isRefinedBy_of_bound lay ρ L hrefl htrans hM hg b hbound h hf).1
      (a, RunItems.start d lay ρ L))

/-- Congruence in the callee over traced runs, by the class alone, with no
budget, for a dialect whose ops show no event and have finitely many
outcomes: in a valid module, replacing the body of its function `@g` with
one under which `@g`, run in the new module from given memories, refines
`@g` in the old, refines every function of the module over its traced runs,
wherever a run names the dialect's memories, calls and recursion included,
whatever the parameter types of `@g` and whatever its new body does to the
memories. -/
theorem Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfin : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; OpsFinite d N (unitsOf lay))
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.traceRuns lay ρ L μ ar M ⊑
      (f.replaceBody g.name b).traceRuns lay ρ L μ ar (M.replaceBody g.name b) := fun a =>
  Func.traceRuns_isRefinedBy_of_from lay ρ L μ ar htrans
    ((Func.memRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ L hrefl htrans hfin hM hg b h hf).1
      (a, RunItems.start d lay ρ L))

end Fir
