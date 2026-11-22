import Fir.Execution.TraceCallsAllowed
import Fir.Execution.TraceArgsFrom

/-!
# Congruence in the callee over traced runs: returns and UB

The engine of `Fir.Execution.TraceCallsAllowed` compares runs of ops. Here
it is read for whole functions, for a dialect that shows events:

* _Returns and UB, call by call._ When the target module runs each call in
  the traced layer as the source does, every return and every UB of a
  function's traced runs from a traced state in the target, on arguments
  that refine the source's and from a traced state that refines the
  source's, is allowed by its traced runs in the source: a return by UB
  after acts that it first shows, refined, or by a return after acts that
  its own refine one by one, of values that its own refine, in a traced
  state that its own refines. So it is for the traced runs from the
  memories a run starts with, whose end of a return its own refines
  (`End.isRefinedBy_of_mem`).
* _Replacing a callee's body gives calls refined._ In a module whose
  symbols are unique, replace the body of its function `@g` with one under
  which `@g`, run in the new module from given traced states, refines `@g`
  in the old. Every call of `@g` is then a traced black box: from traced
  states that refine others, on arguments that refine others, `@g` is
  refined by `@g` from the refined ones (refined arguments from a traced
  state, `Fir.Execution.TraceArgsFrom`), which is refined by the new
  function, by the hypothesis. Every other symbol names the same function in
  both modules.

Divergence of the target across a black box, silent or with acts forever,
needs an argument of its own, since the two runs do not go in step there:
`Fir.Execution.TraceCalleeDiverge` gives it, and
`Fir.Execution.TraceReplaceDiverge` completes congruence in the callee.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectTrace d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) [TyRefinement d.Ty] {M M' : Module d}
  {f : Func d} {a a' : HVector toType (f.params.map (·.2))} {s s' : TraceState N (unitsOf lay)}

/-- A path of a function's traced run in the target that is done is allowed
at some budget by its traced run in the source, from arguments and a traced
state that the target's refine, when every call names the same function in
both modules or a traced black box, and every terminator and every op with
no callee of the function and of the source module's functions is monotone
in the traced layer. -/
theorem Func.traceRunsFrom_tAllowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') (hs : s ⊑ s') {n : Nat}
    {body : List (Operation d)} {env' : Env d} (hen' : f.enter a'.toDVals = .ok (body, env'))
    {e' : TraceEnd (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))
      (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : letI := DialectTrace.stepAt (d := d) lay ρ L
      Func.traceCall (Step (DialectTrace.Acts d)) M' n f env' body s' e') :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    ∃ env, f.enter a.toDVals = .ok (body, env) ∧
      TAllowed (fun N => Func.traceCall (Step (DialectTrace.Acts d)) M N f env body s) e' := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  have hmono' := fun g hg => Func.TraceOpsMonotone.stepAt lay ρ L (hmono g hg)
  have hf' := Func.TraceOpsMonotone.stepAt lay ρ L hf
  obtain ⟨env, hen, henv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy ha) hen'
  exact ⟨env, hen, Func.traceCall_tAllowed (fun e₀ he₀ => Func.traceOps_tAllowed hmono' hcalls n f
    env env' body _ _ hf' (hf'.enter hen') henv (TraceState.IsRefinedBy.enter hs) e₀ he₀) he'⟩

/-- Each return of a function's traced runs from a traced state in the
target is allowed by its traced runs in the source, from arguments and a
traced state that the target's refine: by UB after acts that it first shows,
refined, or by a return after acts that its own refine one by one, of values
and a traced state that its own refine. -/
theorem Func.traceRunsFrom_ret_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') (hs : s ⊑ s') {tr : List (DialectTrace.Acts d)}
    {o' : List (DVal d) × TraceState N (unitsOf lay)}
    (h : traceObservable (f.traceRunsFrom lay ρ L M' (a', s')) (.ret tr o')) :
    ∃ t, traceObservable (f.traceRunsFrom lay ρ L M (a, s)) t ∧ t ⊑ (.ret tr o' : TOutcome _ _) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  obtain ⟨vs', s₁'⟩ := o'
  obtain ⟨n, mt', hx, rfl⟩ := h
  obtain ⟨body, env', hen', k', he'⟩ := Func.traceFrom_ret_iff.1 hx
  obtain ⟨env, hen, hm⟩ := Func.traceRunsFrom_tAllowed lay ρ L hmono hcalls hf ha hs hen' he'
  rcases hm with ⟨N, r, mt, hN, hle⟩ | ⟨N, vs, k, mt, s₁, hN, hvs, hmt, hs₁⟩
  · exact ⟨.ub (Step.actsOf mt) r, ⟨N, mt, Func.traceFrom_ub_iff.2 ⟨_, _, hen, hN⟩, rfl⟩,
      hle.getElem?⟩
  · exact ⟨.ret (Step.actsOf mt) (vs, s₁), ⟨N, mt, Func.traceFrom_ret_iff.2 ⟨_, _, hen, k, hN⟩, rfl⟩,
      hmt, hvs, hs₁⟩

/-- Each UB of a function's traced runs from a traced state in the target is
allowed by UB of its traced runs in the source, from arguments and a traced
state that the target's refine, after acts that it first shows, refined. -/
theorem Func.traceRunsFrom_ub_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') (hs : s ⊑ s') {tr : List (DialectTrace.Acts d)}
    {r' : String} (h : traceObservable (f.traceRunsFrom lay ρ L M' (a', s')) (.ub tr r')) :
    ∃ t, traceObservable (f.traceRunsFrom lay ρ L M (a, s)) t ∧
      t ⊑ (.ub tr r' : TOutcome (DialectTrace.Acts d) (List (DVal d) × TraceState N (unitsOf lay))) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  obtain ⟨n, mt', hx, rfl⟩ := h
  obtain ⟨body, env', hen', he'⟩ := Func.traceFrom_ub_iff.1 hx
  obtain ⟨env, hen, ⟨N, r, mt, hN, hle⟩⟩ :=
    Func.traceRunsFrom_tAllowed lay ρ L hmono hcalls hf ha hs hen' he'
  exact ⟨.ub (Step.actsOf mt) r, ⟨N, mt, Func.traceFrom_ub_iff.2 ⟨_, _, hen, hN⟩, rfl⟩,
    hle.getElem?⟩

/-! # From the memories a run starts with -/

variable (μ : Nat → N) (ar : AddrRule)

omit [TyRefinement d.Ty] in
/-- A return of a function's traced runs is a return of its traced runs from
the memories the run starts with and nothing escaped, seen at its end; and
each such return is one. -/
theorem Func.traceRuns_ret_iff_from {n : Nat} {mt : List (Step (DialectTrace.Acts d))}
    {o : End (unitsOf lay) μ ar (List (DVal d))} :
    f.traceRuns lay ρ L μ ar M a n (.ok (.ok (.ret o), mt)) ↔
      ∃ vs s₁, f.traceRunsFrom lay ρ L M (a, TraceState.init (RunItems.start d lay ρ L)) n
          (.ok (.ok (.ret (vs, s₁)), mt)) ∧
        o = ⟨vs, s₁.mem, s₁.escaped⟩ := by
  constructor
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .ok (.ok (.ret vs), _, s₁), he, ho =>
      cases ho
      exact ⟨vs, s₁, ⟨_, he, rfl⟩, rfl⟩
    | .ok (.ok .fuelExhausted, _, _), _, ho | .ok (.error _, _, _), _, ho | .error _, _, ho =>
      cases ho
  · rintro ⟨vs, s₁, ⟨e, he, ho⟩, rfl⟩
    match e, he, ho with
    | .ok (.ok (.ret _), _, _), he, ho =>
      cases ho
      exact ⟨_, he, rfl⟩
    | .ok (.ok .fuelExhausted, _, _), _, ho | .ok (.error _, _, _), _, ho | .error _, _, ho =>
      cases ho

omit [TyRefinement d.Ty] in
/-- UB of a function's traced runs is UB of its traced runs from the memories
the run starts with and nothing escaped, after the same marked trace; and
each such UB is one. -/
theorem Func.traceRuns_ub_iff_from {n : Nat} {mt : List (Step (DialectTrace.Acts d))} {r : String} :
    f.traceRuns lay ρ L μ ar M a n (.error (r, mt)) ↔
      f.traceRunsFrom lay ρ L M (a, TraceState.init (RunItems.start d lay ρ L)) n
        (.error (r, mt)) := by
  constructor
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .error _, he, ho =>
      cases ho
      exact ⟨_, he, rfl⟩
    | .ok (.ok (.ret _), _, _), _, ho | .ok (.ok .fuelExhausted, _, _), _, ho
    | .ok (.error _, _, _), _, ho => cases ho
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .error _, he, ho =>
      cases ho
      exact ⟨_, he, rfl⟩
    | .ok (.ok (.ret _), _, _), _, ho | .ok (.ok .fuelExhausted, _, _), _, ho
    | .ok (.error _, _, _), _, ho => cases ho

variable [TyPointers d.Ty] {a a' : HVector toType (f.params.map (·.2))}

/-- Each return of a function's traced runs in the target, on arguments that
refine others, a poison by any value, is allowed by its traced runs in the
source on those others: by UB after acts that it first shows, refined, or
by a return after acts that its own refine one by one, whose end of a
return its own refines, when every call names the same function in both
modules or a traced black box, and refinement of values is transitive. -/
theorem Func.traceRuns_calls_ret_allowed
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {tr : List (DialectTrace.Acts d)}
    {o' : End (unitsOf lay) μ ar (List (DVal d))}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M' a') (.ret tr o')) :
    ∃ t, traceObservable (f.traceRuns lay ρ L μ ar M a) t ∧ t ⊑ (.ret tr o' : TOutcome _ _) := by
  obtain ⟨n, mt', hx, rfl⟩ := h
  obtain ⟨vs', s₁', hx', rfl⟩ := (Func.traceRuns_ret_iff_from lay ρ L μ ar).1 hx
  obtain ⟨t, ht, hle⟩ := Func.traceRunsFrom_ret_allowed lay ρ L hmono hcalls hf ha
    (TraceState.isRefinedBy_refl _) ⟨n, mt', hx', rfl⟩
  match t, ht, hle with
  | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
    exact ⟨.ub tr r, ⟨N, mt, (Func.traceRuns_ub_iff_from lay ρ L μ ar).2 hN, htr⟩, hle⟩
  | .ret tr ⟨vs, s₁⟩, ⟨N, mt, hN, htr⟩, ⟨hmt, hvs, hs₁⟩ =>
    refine ⟨.ret tr ⟨vs, s₁.mem, s₁.escaped⟩,
      ⟨N, mt, (Func.traceRuns_ret_iff_from lay ρ L μ ar).2 ⟨vs, s₁, hN, rfl⟩, htr⟩, hmt, ?_⟩
    rw [hs₁.2]
    exact End.isRefinedBy_of_mem (List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans)) _ hvs hs₁.1
  | .diverge _, _, hle | .reacts _, _, hle => exact (hle : False).elim

/-- Each UB of a function's traced runs in the target, on arguments that
refine others, a poison by any value, is allowed by UB of its traced runs in
the source on those others, after acts that it first shows, refined, when
every call names the same function in both modules or a traced black
box. -/
theorem Func.traceRuns_calls_ub_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hcalls : letI := DialectTrace.stepAt (d := d) lay ρ L
      TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M M')
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {tr : List (DialectTrace.Acts d)} {r' : String}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M' a') (.ub tr r')) :
    ∃ t, traceObservable (f.traceRuns lay ρ L μ ar M a) t ∧
      t ⊑ (.ub tr r' : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d)))) := by
  obtain ⟨n, mt', hx, rfl⟩ := h
  obtain ⟨t, ht, hle⟩ := Func.traceRunsFrom_ub_allowed lay ρ L hmono hcalls hf ha
    (TraceState.isRefinedBy_refl _) ⟨n, mt', (Func.traceRuns_ub_iff_from lay ρ L μ ar).1 hx, rfl⟩
  match t, ht, hle with
  | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
    exact ⟨.ub tr r, ⟨N, mt, (Func.traceRuns_ub_iff_from lay ρ L μ ar).2 hN, htr⟩, hle⟩
  | .ret _ _, _, hle | .diverge _, _, hle | .reacts _, _, hle => exact (hle : False).elim

/-! # Replacing a callee's body -/

omit [TyPointers d.Ty] in
/-- In a module whose symbols are unique, the module with `@g`'s new body
runs each call in the traced layer as the module does, when `@g`, run in the
new module from given traced states, refines `@g` in the old: each symbol
other than `@g` names the same function in both, and `@g` is a traced black
box. It asks that every terminator and every op with no callee of the old
module's functions be monotone in the traced layer, that every op have
finitely many outcomes given the world's answers, and that the refinement
of values and of events be transitive. -/
theorem Module.replaceBody_traceCallsRefined
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
    TraceCallsRefined (DialectTrace.Acts d) N (unitsOf lay) M (M.replaceBody g.name b) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  have hobs : ∀ {x y z : List (DVal d) × TraceState N (unitsOf lay)}, x ⊑ y → y ⊑ z → x ⊑ z :=
    fun h₁ h₂ => ⟨List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans) h₁.1 h₂.1,
      TraceState.isRefinedBy_trans h₁.2 h₂.2⟩
  have bb : TraceBlackBox (A := DialectTrace.Acts d) (Mem := N) (unit := unitsOf lay) M
      (M.replaceBody g.name b) g (g.replaceBody g.name b) :=
    { params := rfl
      refines := fun a a' s s' ha hs => TBehaviour.isRefinedBy_trans
        (Act.isRefinedBy_trans htransE) hobs
        (Func.traceRunsFrom_isRefinedBy_of_args lay ρ L hfin hmono (hmono g hg) ha hs) (h (a', s')) }
  refine ⟨fun x => ?_, fun _ _ _ => Module.declares_replaceBody _ _ _ _ _ _⟩
  by_cases hx : x = g.name
  · subst hx
    exact .inr ⟨g, _, Module.func?_of_mem hnd hg, Module.func?_replaceBody_self hnd hg b, bb⟩
  · exact .inl (Module.func?_replaceBody_of_ne hx)

end Fir
