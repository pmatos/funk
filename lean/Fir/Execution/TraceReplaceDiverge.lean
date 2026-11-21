import Fir.Execution.TraceCalleeDiverge
import Fir.Execution.TraceReplace
import Fir.Execution.TraceDiverge

/-!
# Congruence in the callee over traced runs, divergence included

For a dialect that shows events, divergence across black boxes
(`Fir.Execution.TraceCalleeDiverge`) completes the engine of congruence in the
callee over traced runs (`Fir.Execution.TraceReplace`):

* _Calls refined._ When every call names the same function in both modules or
  a traced black box, the traced runs of a function from a traced state in the
  target, on arguments and from a traced state that refine others, refine its
  traced runs in the source on those others: returns, UB, silent divergence
  and acts forever (`Func.traceRunsFrom_isRefinedBy_of_calls`). A target that
  diverges enters its function's entry block, which shows the stream of its
  divergence at every budget; the source's entry block follows it.
* _Replacing a callee's body._ In a module whose symbols are unique, replacing
  the body of its function `@g` with one under which `@g`, run in the new
  module from given traced states, refines `@g` in the old, refines every
  function of the module over its traced runs from given traced states, and
  so over its traced runs from the empty memories
  (`Func.traceRuns_replaceBody_isRefinedBy`). It asks what refined arguments
  over traced runs asks: monotone ops, ops of finitely many outcomes given the
  world's answers (the human's ruling of 2026-11-20, on #233), and transitive
  refinement of values and of events; and reflexive refinement of values.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectTrace d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) [TyRefinement d.Ty] {M M' : Module d}
  {f : Func d}

/-- A stream refined by a closed stream is closed. -/
theorem Stream.IsRefinedBy.closed {A : Type} [HRefinement A A] {S T : Nat → Option A}
    (h : Stream.IsRefinedBy S T) (hT : Stream.Closed T) : Stream.Closed S := fun i hi => by
  have h₁ : (T (i + 1)).isSome := by
    cases hs : T (i + 1) with
    | none => rw [(h (i + 1)).1.2 hs] at hi; cases hi
    | some _ => rfl
  have h₂ := hT i h₁
  cases hs : S i with
  | none => rw [(h i).1.1 hs] at h₂; cases h₂
  | some _ => rfl

/-- Refinement of traced runs from given traced states, for a dialect whose ops
show events, when every call names the same function in both modules or a
traced black box: on arguments that refine others, a poison by any value, and
from a traced state that refines another, the traced runs of a function in the
target refine its traced runs in the source on those others, the traced state
each return ends in included, divergence, silent and with acts forever,
included. It asks that every terminator and every op with no callee of the
function and of the source module's functions be monotone in the traced layer,
and that every op have finitely many outcomes given the world's answers. -/
theorem Func.traceRunsFrom_isRefinedBy_of_calls
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
      traceObservable (f.traceRunsFrom lay ρ L M' (a', s')) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  have div : ∀ t' : TOutcome (DialectTrace.Acts d) (List (DVal d) × TraceState N (unitsOf lay)),
      t'.Diverges → traceObservable (f.traceRunsFrom lay ρ L M' (a', s')) t' →
      ∃ t, traceObservable (f.traceRunsFrom lay ρ L M (a, s)) t ∧ t ⊑ t' := by
    intro t' hdiv ht'
    obtain ⟨K, hK⟩ := TShows.ofObservable ht' hdiv
    obtain ⟨mt₀, hmt₀, -⟩ := hK 0
    obtain ⟨body, env', -, hen', -⟩ := Func.traceFrom_exhausted_iff.1 hmt₀
    have hK' := hK.congr fun n mt => (TCfg.exh_iff_traceFrom (M := M') hen' n mt).symm
    obtain ⟨env, hen, henv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy ha) hen'
    have hf' := Func.TraceOpsMonotone.stepAt lay ρ L hf
    have hc : TCfg.Follows (DialectTrace.Acts d) ⟨f, env, body, { s with mem := s.mem.enter }⟩
        ⟨f, env', body, { s' with mem := s'.mem.enter }⟩ :=
      ⟨rfl, rfl, henv, TraceState.IsRefinedBy.enter hs, hf', hf'.enter hen⟩
    rcases hc.allows (DialectTrace.stepAt_oneStep lay ρ L) (OpsTraceFinite.stepAt lay ρ L hfin)
        (fun g hg => Func.TraceOpsMonotone.stepAt lay ρ L (hmono g hg)) hcalls
        (TOutcome.act?_closed hdiv) hK' with ⟨n, r, mt, hu, hsr⟩ | ⟨S, K₀, hS, hr⟩
    · exact ⟨.ub (Step.actsOf mt) r, ⟨n, mt, Func.traceFrom_ub_iff.2
        ⟨body, env, hen, (TraceM.run_inFrame _ _ _).2 ⟨_, hu, rfl⟩⟩, rfl⟩, hsr⟩
    · have hS' := hS.congr (TCfg.exh_iff_traceFrom (M := M) hen)
      obtain ⟨t₀, ht₀, hdiv₀, hact⟩ := hS'.toObservable (hr.closed (TOutcome.act?_closed hdiv))
      refine ⟨t₀, ht₀, TOutcome.isRefinedBy_of_stream hdiv₀ hdiv fun i => ?_⟩
      rw [hact i]
      exact hr i
  intro t' ht'
  cases t' with
  | ret tr o => exact Func.traceRunsFrom_ret_allowed lay ρ L hmono hcalls hf ha hs ht'
  | ub tr r => exact Func.traceRunsFrom_ub_allowed lay ρ L hmono hcalls hf ha hs ht'
  | diverge tr => exact div _ trivial ht'
  | reacts T => exact div _ trivial ht'

variable (μ : Nat → N) (ar : AddrRule)

omit [TyRefinement d.Ty] in
/-- The traced runs of a function diverge silently after a trace exactly when
its traced runs from the empty memories do: the same paths run out of fuel. -/
theorem Func.traceRuns_diverge_iff_from {a : HVector toType (f.params.map (·.2))}
    {tr : List (DialectTrace.Acts d)} :
    traceObservable (f.traceRuns lay ρ L μ ar M a) (.diverge tr) ↔
      traceObservable (f.traceRunsFrom lay ρ L M (a, TraceState.init)) (.diverge tr) :=
  exists_congr fun _ => forall_congr' fun _ => exists_congr fun _ =>
    and_congr_left' (Func.traceRuns_exhausted_iff_from lay ρ L μ ar)

omit [TyRefinement d.Ty] in
/-- The traced runs of a function show an infinite trace exactly when its
traced runs from the empty memories do: the same paths run out of fuel. -/
theorem Func.traceRuns_reacts_iff_from {a : HVector toType (f.params.map (·.2))}
    {T : Nat → DialectTrace.Acts d} :
    traceObservable (f.traceRuns lay ρ L μ ar M a) (.reacts T) ↔
      traceObservable (f.traceRunsFrom lay ρ L M (a, TraceState.init)) (.reacts T) :=
  exists_congr fun _ => forall_congr' fun _ => exists_congr fun _ =>
    and_congr_left' (Func.traceRuns_exhausted_iff_from lay ρ L μ ar)

variable [TyPointers d.Ty]

/-- When a function's traced runs from the empty memories with nothing escaped
refine another's, the traced state each return ends in included, its traced
runs refine the other's, each return seen at its end, when refinement of
values is transitive. -/
theorem Func.traceRuns_isRefinedBy_of_traceRunsFrom
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {f' : Func d} {a : HVector toType (f.params.map (·.2))}
    {a' : HVector toType (f'.params.map (·.2))}
    (h : traceObservable (f.traceRunsFrom lay ρ L M (a, TraceState.init)) ⊑
      traceObservable (f'.traceRunsFrom lay ρ L M' (a', TraceState.init))) :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑
      traceObservable (f'.traceRuns lay ρ L μ ar M' a') := by
  intro t' ht'
  cases t' with
  | ret tr o' =>
    obtain ⟨n, mt', hx, rfl⟩ := ht'
    obtain ⟨vs', s₁', hx', rfl⟩ := (Func.traceRuns_ret_iff_from lay ρ L μ ar).1 hx
    obtain ⟨t, ht, hle⟩ := h (.ret (Step.actsOf mt') (vs', s₁')) ⟨n, mt', hx', rfl⟩
    match t, ht, hle with
    | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
      exact ⟨.ub tr r, ⟨N, mt, (Func.traceRuns_ub_iff_from lay ρ L μ ar).2 hN, htr⟩, hle⟩
    | .ret tr ⟨vs, s₁⟩, ⟨N, mt, hN, htr⟩, ⟨hmt, hvs, hs₁⟩ =>
      refine ⟨.ret tr ⟨vs, s₁.mem, s₁.escaped⟩,
        ⟨N, mt, (Func.traceRuns_ret_iff_from lay ρ L μ ar).2 ⟨vs, s₁, hN, rfl⟩, htr⟩, hmt, ?_⟩
      rw [hs₁.2]
      exact End.isRefinedBy_of_mem (List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans)) _ hvs
        hs₁.1
    | .diverge _, _, hle | .reacts _, _, hle => exact (hle : False).elim
  | ub tr r' =>
    obtain ⟨n, mt', hx, rfl⟩ := ht'
    obtain ⟨t, ht, hle⟩ := h (.ub (Step.actsOf mt') r')
      ⟨n, mt', (Func.traceRuns_ub_iff_from lay ρ L μ ar).1 hx, rfl⟩
    match t, ht, hle with
    | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
      exact ⟨.ub tr r, ⟨N, mt, (Func.traceRuns_ub_iff_from lay ρ L μ ar).2 hN, htr⟩, hle⟩
    | .ret _ _, _, hle | .diverge _, _, hle | .reacts _, _, hle => exact (hle : False).elim
  | diverge tr' =>
    obtain ⟨t, ht, hle⟩ := h _ ((Func.traceRuns_diverge_iff_from lay ρ L μ ar).1 ht')
    match t, ht, hle with
    | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
      exact ⟨.ub tr r, ⟨N, mt, (Func.traceRuns_ub_iff_from lay ρ L μ ar).2 hN, htr⟩, hle⟩
    | .diverge tr, ht, hle => exact ⟨_, (Func.traceRuns_diverge_iff_from lay ρ L μ ar).2 ht, hle⟩
    | .ret _ _, _, hle | .reacts _, _, hle => exact (hle : False).elim
  | reacts T' =>
    obtain ⟨t, ht, hle⟩ := h _ ((Func.traceRuns_reacts_iff_from lay ρ L μ ar).1 ht')
    match t, ht, hle with
    | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
      exact ⟨.ub tr r, ⟨N, mt, (Func.traceRuns_ub_iff_from lay ρ L μ ar).2 hN, htr⟩, hle⟩
    | .reacts T, ht, hle => exact ⟨_, (Func.traceRuns_reacts_iff_from lay ρ L μ ar).2 ht, hle⟩
    | .ret _ _, _, hle | .diverge _, _, hle => exact (hle : False).elim

/-! # Replacing a callee's body -/

omit [TyPointers d.Ty] in
/-- Congruence in the callee over traced runs from given traced states, for a
dialect whose ops show events: in a module whose symbols are unique, replacing
the body of its function `@g` with one under which `@g`, run in the new module
from given traced states, refines `@g` in the old, refines every function of
the module over its traced runs from given traced states, divergence included.
It asks that every terminator and every op with no callee of the old module's
functions be monotone in the traced layer, that every op have finitely many
outcomes given the world's answers, that the refinement of values be
reflexive and transitive, and that the refinement of events be transitive. -/
theorem Func.traceRunsFrom_replaceBody_isRefinedBy
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
      (f.replaceBody g.name b).traceRunsFrom lay ρ L (M.replaceBody g.name b) := by
  by_cases hfg : f.name = g.name
  · rw [eq_of_nodup_map hnd hf hg hfg]
    exact h
  show f.traceRunsFrom lay ρ L M ⊑ Func.traceRunsFrom lay ρ L _
    { f with body := if f.name = g.name then b else f.body }
  rw [ite_eq_right hfg]
  exact fun p => Func.traceRunsFrom_isRefinedBy_of_calls lay ρ L hfin hmono
    (Module.replaceBody_traceCallsRefined lay ρ L hfin hmono htrans htransE hnd hg b h) (hmono f hf)
    (HVector.forall₂_refl (fun v => hrefl v) p.1) (TraceState.isRefinedBy_refl p.2)

/-- Congruence in the callee over traced runs, for a dialect whose ops show
events: in a module whose symbols are unique, replacing the body of its
function `@g` with one under which `@g`, run in the new module from given
traced states, refines `@g` in the old, refines every function of the module
over its traced runs, the end of each return included, divergence, silent and
with acts forever, included. It asks what congruence in the callee from given
traced states asks. -/
theorem Func.traceRuns_replaceBody_isRefinedBy
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
      (f.replaceBody g.name b).traceRuns lay ρ L μ ar (M.replaceBody g.name b) := fun a =>
  Func.traceRuns_isRefinedBy_of_traceRunsFrom lay ρ L μ ar htrans
    (Func.traceRunsFrom_replaceBody_isRefinedBy lay ρ L hfin hmono hrefl htrans htransE hnd hg b h hf
      (a, TraceState.init))

end Fir
