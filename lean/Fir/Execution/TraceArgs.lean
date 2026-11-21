import Fir.Execution.TraceOpsRefine
import Fir.Execution.TraceObligationLaws

/-!
# Refined arguments over traced runs: returns, UB and each budget

A function's traced runs on arguments that refine others go in step with its
traced runs on those others (`Fir.Execution.TraceOpsRefine`). The run of a
function enters its entry block's ops in a frame, as a call does, so at
every budget each path of the run on the refined arguments that is not
stuck is allowed by a path of the run on the others, at the same budget:

* a return of values, after acts, in a traced state, is allowed by a return
  of values that they refine, after acts that they refine one by one, in a
  traced state that it refines, or by UB;
* running out of fuel after acts is allowed by running out of fuel after
  acts that they refine one by one, or by UB;
* UB after acts is allowed by UB after acts that they first show, refined.

So, for a dialect whose ops show events, in a module whose terminators and
ops with no callee are monotone in the traced layer, each return and each
UB of the traced runs of a function on arguments that refine others, a
poison by any value, is allowed by its traced runs on those others: a
return by UB after acts that the return first shows, refined, or by a
return after acts that its own refine one by one, whose end of a return is
refined by its own, since memories that refine others, with the same
allocations escaped, give ends that refine each other
(`End.isRefinedBy_of_mem`). At each budget, each path that runs out of fuel
is allowed in the same way. Divergence needs one trace of the source for
every budget, which the next stage of #233 gives under its hypothesis that
each op has finitely many outcomes given the world's answers.
-/

namespace Fir

open Memory

/-! # The run of a function in the traced layer -/

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {B : Type} [HRefinement B B]
  {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty]

/-- What a path of a source's run of a function ends with allows what a path
of the target's run ends with: a return allows a return of values that
refine its own, and running out of fuel allows running out of fuel. -/
def Result.Finished : Except Stuck (Result (List (DVal d))) →
    Except Stuck (Result (List (DVal d))) → Prop
  | .ok (.ret vs), .ok (.ret vs') => vs ⊑ vs'
  | .ok .fuelExhausted, .ok .fuelExhausted => True
  | _, _ => False

/-- How a path of a run of a function ends, from how its entry block's ops end
in its frame: a return gives back the values, without the steps left. -/
def Result.finishEnd {σ : Type} :
    TraceEnd B σ (Except Stuck (Result (List (DVal d) × Nat))) →
      TraceEnd B σ (Except Stuck (Result (List (DVal d))))
  | .ok (.ok (.ret (vs, _)), t, s) => .ok (.ok (.ret vs), t, s)
  | .ok (.ok .fuelExhausted, t, s) => .ok (.ok .fuelExhausted, t, s)
  | .ok (.error st, t, s) => .ok (.error st, t, s)
  | .error u => .error u

/-- Finishing keeps a way of ending allowing another in step. -/
theorem TraceEnd.Allows.finishEnd :
    ∀ {e e' : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))},
      TraceEnd.Allows Result.InStep e e' →
      TraceEnd.Allows Result.Finished (Result.finishEnd e) (Result.finishEnd e')
  | .ok (.ok (.ret _), _, _), .ok (.ok (.ret _), _, _), h => ⟨h.1.1, h.2⟩
  | .ok (.ok .fuelExhausted, _, _), .ok (.ok .fuelExhausted, _, _), h => ⟨trivial, h.2⟩
  | .error _, .ok (.ok (.ret _), _, _), h | .error _, .ok (.ok .fuelExhausted, _, _), h
  | .error _, .ok (.error _, _, _), h | .error _, .error _, h => h
  | .ok (.ok (.ret _), _, _), .ok (.ok .fuelExhausted, _, _), h
  | .ok (.ok .fuelExhausted, _, _), .ok (.ok (.ret _), _, _), h
  | .ok (.error _, _, _), .ok _, h | .ok (.ok (.ret _), _, _), .ok (.error _, _, _), h
  | .ok (.ok .fuelExhausted, _, _), .ok (.error _, _, _), h => h.1.elim
  | .ok _, .error _, h => h.elim

variable [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))]

omit [HRefinement B B] [TyRefinement d.Ty] in
/-- A path of the traced run of a function that is not stuck finishes a path
of its entry block's ops in its frame. -/
theorem Func.traceRun_iff {M : Module d} {f : Func d} {a : HVector toType (f.params.map (·.2))}
    {n : Nat} {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d))))}
    (hne : TraceEnd.NotStuck e) :
    (f.run M (m := TraceM B (TraceState Mem unit)) a n).run s e ↔
      ∃ body env, f.enter a.toDVals = .ok (body, env) ∧
        ∃ e₀, Func.traceCall B M n f env body s e₀ ∧ e = Result.finishEnd e₀ := by
  simp only [Func.run]
  rw [TraceM.run_liftExcept_bind hne]
  constructor
  · rintro ⟨⟨body, env⟩, hen, h⟩
    refine ⟨body, env, hen, ?_⟩
    rcases (TraceM.run_except_bind _ _ _ _).1 h with
      ⟨x, t, s', e', hx, h, rfl⟩ | ⟨st, t, s', hx, rfl⟩ | ⟨r, t, hx, rfl⟩
    · rcases x with ⟨vs, k⟩ | _
      · have h : e' = _ := h
        subst h
        exact ⟨_, hx, by simp [TraceEnd.after, Result.finishEnd]⟩
      · have h : e' = _ := h
        subst h
        exact ⟨_, hx, by simp [TraceEnd.after, Result.finishEnd]⟩
    · exact absurd rfl (hne st t s')
    · exact ⟨_, hx, rfl⟩
  · rintro ⟨body, env, hen, e₀, h₀, rfl⟩
    refine ⟨(body, env), hen, ?_⟩
    rcases e₀ with ⟨r, t⟩ | ⟨x, t, s'⟩
    · exact (TraceM.run_except_bind _ _ _ _).2 (.inr (.inr ⟨r, t, h₀, rfl⟩))
    · rcases x with st | (⟨vs, k⟩ | _)
      · exact absurd rfl (hne st t s')
      · exact (TraceM.run_except_bind _ _ _ _).2
          (.inl ⟨_, t, s', _, h₀, rfl, by simp [TraceEnd.after, Result.finishEnd]⟩)
      · exact (TraceM.run_except_bind _ _ _ _).2
          (.inl ⟨_, t, s', _, h₀, rfl, by simp [TraceEnd.after, Result.finishEnd]⟩)

/-- At every budget, every path of a function's traced run on arguments that
refine others, from a traced state that refines another, that is not stuck,
is allowed by a path of its traced run on those others, from that other
state, at the same budget, when every terminator and every op with no
callee of the function and of the module's functions is monotone in the
traced layer. -/
theorem Func.traceRun_allowed {M : Module d}
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone B (TraceState Mem unit)) {f : Func d}
    (hf : f.TraceOpsMonotone B (TraceState Mem unit)) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {s s' : TraceState Mem unit} (hS : s ⊑ s') (n : Nat)
    {e' : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d))))}
    (he' : (f.run M (m := TraceM B (TraceState Mem unit)) a' n).run s' e')
    (hne : TraceEnd.NotStuck e') :
    ∃ e, (f.run M (m := TraceM B (TraceState Mem unit)) a n).run s e ∧
      TraceEnd.Allows Result.Finished e e' := by
  obtain ⟨body, env', hen', e₀', h₀', rfl⟩ := (Func.traceRun_iff hne).1 he'
  obtain ⟨env, hen, henv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy ha) hen'
  have hne₀ : TraceEnd.NotStuck e₀' := by
    rintro st t s₁ rfl
    exact hne st t s₁ rfl
  obtain ⟨e₀, he₀, hle⟩ := Func.traceCall_allowed (fun e₁' he₁' hne₁ =>
    Func.traceOps_allowed hmono n f env env' body _ _ hf (hf.enter hen') henv
      (TraceState.IsRefinedBy.enter hS) e₁' he₁' hne₁) h₀' hne₀
  have hfin := hle.finishEnd
  exact ⟨_, (Func.traceRun_iff (hfin.notStuck fun _ _ h => h)).2 ⟨body, env, hen, e₀, he₀, rfl⟩, hfin⟩

end


/-! # The traced runs of a dialect with events -/

/-- A list refined by a prefix of another is refined, at each of its places,
by the other's element there. -/
theorem List.IsRefinedPrefix.getElem? {A : Type} [HRefinement A A] {l l' : List A}
    (h : List.IsRefinedPrefix l l') (i : Nat) (a : A) (ha : l[i]? = some a) :
    ∃ b, l'[i]? = some b ∧ a ⊑ b := by
  obtain ⟨m, hm, r, rfl⟩ := h
  obtain ⟨b, hb, hab⟩ := List.IsRefinedBy.getElem?_some hm i a ha
  have hi : i < m.length := (List.getElem?_eq_some_iff.1 hb).1
  exact ⟨b, by rw [List.getElem?_append_left hi]; exact hb, hab⟩

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty] {N : Type}
  [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
  (μ : Nat → N) (ar : AddrRule) {M : Module d} {f : Func d}

/-- At every budget, every path of a function's traced runs on arguments that
refine others that is not stuck comes from a path of its run in the traced
layer of marked traces that is allowed by a path of its run on those
others, which its traced runs on those others come from, when every
terminator and every op with no callee of the function and of the module's
functions is monotone in the traced layer. -/
theorem Func.traceRuns_path_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {n : Nat} {o : Except (String × List (Step (DialectTrace.Acts d)))
      (Except Stuck (Result (End (unitsOf lay) μ ar (List (DVal d)))) ×
        List (Step (DialectTrace.Acts d)))}
    (hx : f.traceRuns lay ρ L μ ar M a' n o) (hne : ∀ st mt, o ≠ .ok (.error st, mt)) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    ∃ e e', (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) a n).run
        (TraceState.init (RunItems.start d lay ρ L)) e ∧
      (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) a' n).run
        (TraceState.init (RunItems.start d lay ρ L)) e' ∧
      o = e'.map (fun p => (p.2.2.endOf μ ar p.1, p.2.1)) ∧ TraceEnd.Allows Result.Finished e e' := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  obtain ⟨e', he', rfl⟩ := hx
  have hne' : TraceEnd.NotStuck e' := by
    rintro st t s rfl
    exact hne st t rfl
  obtain ⟨e, he, hle⟩ := Func.traceRun_allowed
    (fun g hg => Func.TraceOpsMonotone.stepAt lay ρ L (hmono g hg))
    (Func.TraceOpsMonotone.stepAt lay ρ L hf) ha (TraceState.isRefinedBy_refl _) n he' hne'
  exact ⟨e, e', he, he', rfl, hle⟩


variable {a a' : HVector toType (f.params.map (·.2))}

/-- At every budget, each path of a function's traced runs on arguments that
refine others that runs out of fuel is allowed by a path of its traced runs
on those others at the same budget: one that runs out of fuel after acts
that its own refine one by one, or UB after acts that it first shows,
refined. -/
theorem Func.traceRuns_exhausted_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {n : Nat}
    {mt' : List (Step (DialectTrace.Acts d))}
    (hx : f.traceRuns lay ρ L μ ar M a' n (.ok (.ok .fuelExhausted, mt'))) :
    (∃ mt, f.traceRuns lay ρ L μ ar M a n (.ok (.ok .fuelExhausted, mt)) ∧ mt ⊑ mt') ∨
      ∃ r mt, f.traceRuns lay ρ L μ ar M a n (.error (r, mt)) ∧ List.IsRefinedPrefix mt mt' := by
  obtain ⟨e, e', he, -, ho, hle⟩ :=
    Func.traceRuns_path_allowed lay ρ L μ ar hmono hf ha hx (fun _ _ h => by cases h)
  rcases e' with ⟨_, _⟩ | ⟨y', t', s'⟩
  · cases ho
  rcases y' with _ | (_ | _) <;>
    simp only [Except.map, TraceState.endOf, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
      false_and] at ho
  obtain ⟨-, rfl⟩ := ho
  rcases e with ⟨r, t⟩ | ⟨y, t, s₁⟩
  · exact .inr ⟨r, t, ⟨_, he, rfl⟩, hle⟩
  · rcases y with _ | (_ | _)
    · exact hle.1.elim
    · exact hle.1.elim
    · exact .inl ⟨t, ⟨_, he, rfl⟩, hle.2.1⟩

variable [TyPointers d.Ty]

/-- Each UB of a function's traced runs on arguments that refine others is
allowed by UB of its traced runs on those others, after acts that it first
shows, refined. -/
theorem Func.traceRuns_ub_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {tr : List (DialectTrace.Acts d)} {r' : String}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M a') (.ub tr r')) :
    ∃ s : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d))),
      traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧
        s ⊑ (.ub tr r' : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d)))) := by
  obtain ⟨n, mt', hx, rfl⟩ := h
  obtain ⟨e, e', he, -, ho, hle⟩ :=
    Func.traceRuns_path_allowed lay ρ L μ ar hmono hf ha hx (fun _ _ h => by cases h)
  rcases e' with ⟨_, t'⟩ | ⟨_, _, _⟩ <;> simp only [Except.map, Except.error.injEq, Prod.mk.injEq,
    reduceCtorEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  rcases e with ⟨r, t⟩ | ⟨_, _, _⟩
  · exact ⟨.ub (Step.actsOf t) r, ⟨n, t, ⟨_, he, rfl⟩, rfl⟩,
      (Step.actsOf_isRefinedPrefix hle).getElem?⟩
  · exact hle.elim


/-- Each return of a function's traced runs on arguments that refine others,
a poison by any value, is allowed by its traced runs on those others: by UB
after acts that it first shows, refined, or by a return after acts that its
own refine one by one, whose end of a return its own refines, when the
refinement of values is transitive. -/
theorem Func.traceRuns_ret_allowed
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {tr : List (DialectTrace.Acts d)}
    {o' : End (unitsOf lay) μ ar (List (DVal d))}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M a') (.ret tr o')) :
    ∃ s : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d))),
      traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧
        s ⊑ (.ret tr o' : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d)))) := by
  obtain ⟨n, mt', hx, rfl⟩ := h
  obtain ⟨e, e', he, -, ho, hle⟩ :=
    Func.traceRuns_path_allowed lay ρ L μ ar hmono hf ha hx (fun _ _ h => by cases h)
  rcases e' with ⟨_, _⟩ | ⟨y', t', s'⟩
  · cases ho
  rcases y' with _ | (vs' | _) <;>
    simp only [Except.map, TraceState.endOf, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
      false_and, Result.ret.injEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  rcases e with ⟨r, t⟩ | ⟨y, t, s₁⟩
  · exact ⟨.ub (Step.actsOf t) r, ⟨n, t, ⟨_, he, rfl⟩, rfl⟩,
      (Step.actsOf_isRefinedPrefix hle).getElem?⟩
  · rcases y with _ | (vs | _)
    · exact hle.1.elim
    · obtain ⟨hvs, ht, hS, hesc⟩ := hle
      refine ⟨.ret (Step.actsOf t) ⟨vs, s₁.mem, s₁.escaped⟩, ⟨n, t, ⟨_, he, rfl⟩, rfl⟩,
        Step.actsOf_isRefinedBy ht, ?_⟩
      rw [hesc]
      exact End.isRefinedBy_of_mem (List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans)) _
        hvs hS
    · exact hle.1.elim

end

end Fir
