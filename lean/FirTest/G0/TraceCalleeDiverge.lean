import Fir
import FirRef

/-!
G0's check on the Lean side, for congruence in the callee over traced runs with
divergence (ADR-2026-11-03-0600, `docs/decisions/semantics-m1-trace-refinement.md`),
split from `FirTest.G0` by subject. Each statement below is made of an
arbitrary dialect `d` with the spec's own proof, so it builds only while
those stay parameterized over the dialect. `scripts/check_g0.py` checks this
file as it checks the other files of `FirTest/G0/`.

They restate the engine of congruence in the callee for a dialect whose ops
show events, divergence included (stage 3c-2 of #233), under the human's
ruling of 2026-11-20 that each op has finitely many outcomes given the world's
answers: the traced runs of a function refine across modules whose calls are
refined, and replacing a callee's body by one that refines it refines every
function, from given traced states and from the memories a run starts
with. For a dialect whose ops show no event, the bridge from runs with
memory to traced runs from a traced state is restated too (stage 3c-2b).
-/

namespace FirTest.G0

open Fir Fir.Memory

/-- For every function of every dialect whose ops show events, are monotone
in the traced layer and have finitely many outcomes given the world's
answers, its traced runs from a traced state in a target module whose calls
refine the source's, on arguments that refine others, refine its traced runs
in the source on those others from a traced state that it refines,
divergence included. -/
theorem traceRunsFrom_isRefinedBy_of_calls (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    {M M' : Module d} {f : Func d}
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {s s' : TraceState N (unitsOf lay)} (hs : s ⊑ s') :
    traceObservable (f.traceRunsFrom lay ρ L M (a, s)) ⊑
      traceObservable (f.traceRunsFrom lay ρ L M' (a', s')) :=
  Func.traceRunsFrom_isRefinedBy_of_calls lay ρ L hfin hmono hcalls hf ha hs

/-- For every dialect whose ops show events, replacing the body of a function
`@g` of a module whose symbols are unique with one under which `@g`, run in
the new module from given traced states, refines `@g` in the old, refines
every function of the module over its traced runs from given traced states,
divergence included. -/
theorem traceRunsFrom_replaceBody_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    {M : Module d} {f : Func d}
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (htransE : ∀ {e₁ e₂ e₃ : DialectTrace.Event d}, e₁ ⊑ e₂ → e₂ ⊑ e₃ → e₁ ⊑ e₃)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : g.traceRunsFrom lay ρ L M ⊑
      (g.replaceBody g.name b).traceRunsFrom lay ρ L (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.traceRunsFrom lay ρ L M ⊑
      (f.replaceBody g.name b).traceRunsFrom lay ρ L (M.replaceBody g.name b) :=
  Func.traceRunsFrom_replaceBody_isRefinedBy lay ρ L hfin hmono hrefl htrans htransE hnd hg b h hf

/-- For every dialect whose ops show events, the same replacement refines every
function of the module over its traced runs, each return seen at its end,
divergence included. -/
theorem traceRuns_replaceBody_isRefinedBy_of_traceFinite (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    [TyPointers d.Ty] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule) {M : Module d}
    {f : Func d}
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (htransE : ∀ {e₁ e₂ e₃ : DialectTrace.Event d}, e₁ ⊑ e₂ → e₂ ⊑ e₃ → e₁ ⊑ e₃)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : g.traceRunsFrom lay ρ L M ⊑
      (g.replaceBody g.name b).traceRunsFrom lay ρ L (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.traceRuns lay ρ L μ ar M ⊑
      (f.replaceBody g.name b).traceRuns lay ρ L μ ar (M.replaceBody g.name b) :=
  Func.traceRuns_replaceBody_isRefinedBy lay ρ L μ ar hfin hmono hrefl htrans htransE hnd hg b h hf

/-- For every dialect whose ops show no event, with its traced semantics the
lift of its semantics with memory, a function's runs from the memories of a
traced state that refine another's give traced runs from that state that
refine the other's, the traced state each return ends in included. -/
theorem traceRunsFrom_isRefinedBy_of_memRunsFrom (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    {M M' : Module d} {f f' : Func d} {a : HVector toType (f.params.map (·.2))}
    {a' : HVector toType (f'.params.map (·.2))} {s : TraceState N (unitsOf lay)}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      observable (f.memRunsFrom M (a, s.mem)) ⊑ observable (f'.memRunsFrom M' (a', s.mem))) :
    letI := DialectTrace.ofMem d
    traceObservable (f.traceRunsFrom lay ρ L M (a, s)) ⊑
      traceObservable (f'.traceRunsFrom lay ρ L M' (a', s)) :=
  Func.traceRunsFrom_isRefinedBy_of_memRunsFrom lay ρ L h

end FirTest.G0
