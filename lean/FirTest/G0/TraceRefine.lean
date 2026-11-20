import Fir
import FirRef

/-!
G0's check on the Lean side, for refinement over traced runs (ADR-2026-11-03-0600,
`docs/decisions/semantics-m1-trace.md`), split from `FirTest.G0` by subject.
Each statement below is made of an arbitrary dialect `d`, or an arbitrary
base and extension, with the spec's own proof, so it builds only while those
stay parameterized over the dialect. `scripts/check_g0.py` checks this file
as it checks the other files of `FirTest/G0/`.

They restate, over traced runs, for every dialect whose ops show no event,
the refinement results: refined arguments, and congruence in the callee
with a budget for the new callee or, when the dialect's ops have finitely
many outcomes, with none, each from what holds with memory; that a
dialect's semantics with memory, lifted, is a traced semantics that lifts
it; and that a sum's values hold pointers when both sides' do. A dialect
whose ops show events needs the theorems of the traced layer itself, which
stages 3b and 3c of #233 give.
-/

namespace FirTest.G0

open Fir Fir.Memory

/-! # A dialect with no event -/

/-- Every dialect's semantics with memory, lifted onto the memories of the
traced state, is a traced semantics that lifts it. -/
theorem ofMem_liftsMem (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] :
    @LiftsMem d _ _ _ _ _ _ (DialectTrace.ofMem d) :=
  DialectTrace.ofMem_liftsMem d

/-- The values of every sum hold pointers when both sides' do. -/
example (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty] [TyRefinement base.Ty]
    [TyRefinement e.Ty] [TyPointers base.Ty] [TyPointers e.Ty] : TyPointers (base ⊞ e).Ty :=
  inferInstance

/-! # Refinement over traced runs -/

/-- For every function of every dialect whose ops show no event, when its
runs from the empty memories refine another's, the memories they end with
included, its traced runs refine the other's. -/
theorem traceRuns_isRefinedBy_of_from (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [TyRefinement d.Ty] [TyPointers d.Ty] [DialectTrace d] [LiftsMem d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M M' : Module d} {f f' : Func d} {a : HVector toType (f.params.map (·.2))}
    {a' : HVector toType (f'.params.map (·.2))}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      observable (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay)))) ⊑
        observable (f'.memRunsFrom M' (a', (Memories.empty : Memories N (unitsOf lay))))) :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑
      traceObservable (f'.traceRuns lay ρ L μ ar M' a') :=
  Func.traceRuns_isRefinedBy_of_from lay ρ L μ ar htrans h

/-- Refined arguments over traced runs, for every function of a module whose
functions are valid, of every dialect lawful in its monotonicity whose ops
show no event, wherever a run names its memories, at every world. -/
theorem traceRuns_args_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [TyPointers d.Ty] [LawfulDialectMonotone d]
    [DialectTrace d] [LiftsMem d] [Inhabited (DialectTrace.Answer d)] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {ctx : ModuleContext d} {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func d}
    (hf : f ∈ M.funcs) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    ∀ w t, (traceObservable (f.traceRuns lay ρ L μ ar M a')).atWorld w t →
      ∃ s, traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧ s ⊑ t :=
  TBehaviour.isRefinedBy_iff_world.1
    (Func.traceRuns_args_isRefinedBy_of_lawful lay ρ L μ ar htrans hv hf ha)

/-- Congruence in the callee over traced runs, for every function of a valid
module of every dialect lawful in its monotonicity whose ops show no event,
wherever a run names its memories, when the new body, run from given
memories, refines the old one and has one budget past which it runs out of
fuel only if it diverges. -/
theorem traceRuns_replaceBody_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [TyPointers d.Ty] [LawfulDialectMonotone d]
    [DialectTrace d] [LiftsMem d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hbound : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.traceRuns lay ρ L μ ar M ⊑
      (f.replaceBody g.name b).traceRuns lay ρ L μ ar (M.replaceBody g.name b) :=
  Func.traceRuns_replaceBody_isRefinedBy_of_bound lay ρ L μ ar hrefl htrans hM hg b hbound h hf

/-- Congruence in the callee over traced runs, with no budget, for every
function of a valid module of every dialect lawful in its monotonicity whose
ops show no event and have finitely many outcomes, wherever a run names its
memories, when the new body, run from given memories, refines the old one,
at every world. -/
theorem traceRuns_replaceBody_isRefinedBy_of_opsFinite (d : Dialect) [TyDenote d.Ty]
    [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [TyPointers d.Ty] [LawfulDialectMonotone d]
    [DialectTrace d] [LiftsMem d] [Inhabited (DialectTrace.Answer d)] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfin : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; OpsFinite d N (unitsOf lay))
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    ∀ a w t, (traceObservable ((f.replaceBody g.name b).traceRuns lay ρ L μ ar
        (M.replaceBody g.name b) a)).atWorld w t →
      ∃ s, traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧ s ⊑ t :=
  FuncTraceRuns.isRefinedBy_iff_world.1
    (Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ L μ ar hrefl htrans hfin hM hg b h
      hf)

end FirTest.G0
