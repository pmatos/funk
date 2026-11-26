import Fir
import FirRef

/-!
G0's check on the Lean side, for congruence in the callee over traced runs
(ADR-2026-11-03-0600, `docs/decisions/semantics-m1-trace-refinement.md`),
split from `FirTest.G0` by subject. Each statement below is made of an
arbitrary dialect `d` with the spec's own proof, so it builds only while
those stay parameterized over the dialect. `scripts/check_g0.py` checks this
file as it checks the other files of `FirTest/G0/`.

They restate the engine of congruence in the callee for a dialect whose ops
show events, without divergence (stage 3c-1 of #233): more fuel keeps a
return and UB; every return and UB of the target's traced run, call by call,
is allowed by the source's at some budget; refined arguments from a given
traced state, in full, under the human's ruling of 2026-11-20 that each op
has finitely many outcomes given the world's answers; and that replacing a
callee's body by one that refines it gives calls refined.
-/

namespace FirTest.G0

open Fir Fir.Memory

/-- In every traced layer, a traced run of ops of every dialect with more
fuel returns as it did, with as many more steps left, and hits UB as it
did. -/
theorem traceOps_up {B : Type} (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
    [DialectDenote d (TraceM B (TraceState Mem unit))]
    [DialectExtCall d (TraceM B (TraceState Mem unit))] {M : Module d} (j n : Nat) (f : Func d)
    (env : Env d) (os : List (Operation d)) (s : TraceState Mem unit)
    (e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat))))
    (h : Func.traceOps B M n f env os s e) (hd : e.Done) :
    Func.traceOps B M (n + j) f env os s (e.addLeft j) :=
  Func.traceOps_up j n f env os s e h hd

/-- For every dialect, every return and UB of the target's traced run of ops
is allowed by the source's at some budget, comparing acts, when every call
names the same function in both modules or a traced black box, from a pair
of configurations of a guard. -/
theorem traceOps_tAllowed {A : Type} [HRefinement A A] (d : Dialect) [TyDenote d.Ty]
    [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [TyRefinement d.Ty] {Mem : Type}
    {unit : Mem → Nat} [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))]
    {agree : List (DVal d) → TraceState Mem unit → List (DVal d) → TraceState Mem unit → Prop}
    {G : TCfg d Mem unit → TCfg d Mem unit → Prop}
    {M M' : Module d} (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step A) (TraceState Mem unit) agree)
    (hcalls : TraceCallsRefined A Mem unit M M') (hG : TCfg.Guard A agree M M' G) (n : Nat)
    (f : Func d) (env env' : Env d) (os : List (Operation d)) (s s' : TraceState Mem unit)
    (hf : f.TraceOpsMonotone (Step A) (TraceState Mem unit) agree)
    (hops : TraceMonotoneOps (Step A) (TraceState Mem unit) os agree) (henv : env.IsRefinedBy env')
    (hs : s ⊑ s') (hGc : G ⟨f, env, os, s⟩ ⟨f, env', os, s'⟩)
    (e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat))))
    (he' : Func.traceOps (Step A) M' n f env' os s' e') :
    TAllowed (fun N => Func.traceOps (Step A) M N f env os s) e' :=
  Func.traceOps_tAllowed hmono hcalls hG n f env env' os s s' hf hops henv hs hGc e' he'

/-- For every function of every dialect whose ops show events, are monotone
in the traced layer and have finitely many outcomes given the world's
answers, its traced runs from a traced state, on arguments that refine
others, refine its traced runs on those others from a traced state that it
refines, the traced state each return ends in included. -/
theorem traceRunsFrom_isRefinedBy_of_args (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    {M : Module d} {f : Func d}
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {s s' : TraceState N (unitsOf lay)} (hs : s ⊑ s') :
    traceObservable (f.traceRunsFrom lay ρ L M (a, s)) ⊑
      traceObservable (f.traceRunsFrom lay ρ L M (a', s')) :=
  Func.traceRunsFrom_isRefinedBy_of_args lay ρ L hfin hmono hf ha hs

/-- For every dialect whose ops show events, replacing the body of a function
`@g` of a module whose symbols are unique with one under which `@g`, run in
the new module from given traced states, refines `@g` in the old, makes
every call of the new module refine the old one's in the traced layer. -/
theorem replaceBody_traceCallsRefined (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    {M : Module d}
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (htransE : ∀ {e₁ e₂ e₃ : DialectTrace.Event d}, e₁ ⊑ e₂ → e₂ ⊑ e₃ → e₁ ⊑ e₃)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : g.traceRunsFrom lay ρ L M ⊑
      (g.replaceBody g.name b).traceRunsFrom lay ρ L (M.replaceBody g.name b)) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M (M.replaceBody g.name b) :=
  Module.replaceBody_traceCallsRefined lay ρ L hfin hmono htrans htransE hnd hg b h

/-- For every function of every dialect whose ops show events, each return
of its traced runs in a target module that runs each call as the source
does, in the traced layer, on arguments that refine others, is allowed by
its traced runs in the source on those others. -/
theorem traceRuns_calls_ret_allowed (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    [TyPointers d.Ty] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule) {M M' : Module d}
    {f : Func d}
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {tr : List (DialectTrace.Acts d)} {o' : End (unitsOf lay) μ ar (List (DVal d))}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M' a') (.ret tr o')) :
    ∃ t, traceObservable (f.traceRuns lay ρ L μ ar M a) t ∧ t ⊑ (.ret tr o' : TOutcome _ _) :=
  Func.traceRuns_calls_ret_allowed lay ρ L μ ar htrans hmono hcalls hf ha h

/-- For every function of every dialect whose ops show events, each UB of its
traced runs in a target module that runs each call as the source does, in
the traced layer, on arguments that refine others, is allowed by UB of its
traced runs in the source on those others. -/
theorem traceRuns_calls_ub_allowed (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    [TyPointers d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule) {M M' : Module d} {f : Func d}
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {tr : List (DialectTrace.Acts d)} {r' : String}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M' a') (.ub tr r')) :
    ∃ t, traceObservable (f.traceRuns lay ρ L μ ar M a) t ∧
      t ⊑ (.ub tr r' : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d)))) :=
  Func.traceRuns_calls_ub_allowed lay ρ L μ ar hmono hcalls hf ha h

end FirTest.G0
