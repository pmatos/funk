import Fir.Execution.TraceArgsFrom

/-!
# Refined arguments over traced runs, divergence included

A function's traced runs truncate and, when every op has finitely many
outcomes given the world's answers, have finitely many traces at each
budget:

* _They truncate._ A path of a function's traced runs at a budget is its
  entry block's ops, run in a frame. Cut at a smaller budget
  (`Fir.Execution.TraceTruncate`), a path that runs out of fuel gives one
  that runs out of fuel there, after a marked trace that starts its own,
  with at most as many steps as the budget. When it shows less, it has
  spent at most `W` steps of fuel on each step, where `W` bounds the chains
  of calls of the module (`Fir.Execution.TraceChain`), so it keeps the
  longer path's first `N` steps when `W (N + 1)` is at most its budget.
* _Finitely many traces at a budget_: the entry block's ops have finitely
  many outcomes at the budget, given the world's answers
  (`Fir.Execution.TraceFiniteRuns`).

With the paths that run out of fuel allowed at each budget
(`Fir.Execution.TraceArgs`), König's lemma (`Fir.Execution.TraceKonig`)
gives divergence. So, for a dialect whose ops show events, in a module whose
terminators and ops with no callee are monotone in the traced layer, and
whose ops each have finitely many outcomes given the world's answers (the
hypothesis that the human ruled on 2026-11-20, on #233, in the form by
position of `Fir.Execution.TraceFinite`), the traced runs of a function on
arguments that refine others, a poison by any value, refine its traced runs
on those others: returns, UB, silent divergence and acts forever.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectTrace d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule) {M : Module d}
  {f : Func d}

/-- A path of a function's traced runs that runs out of fuel is a path of its
entry block's ops in a frame, from the empty memories with nothing escaped,
that runs out of fuel after the same marked trace; and each such path is
one. -/
theorem Func.traceRuns_exhausted_iff {a : HVector toType (f.params.map (·.2))} {n : Nat}
    {mt : List (Step (DialectTrace.Acts d))} :
    f.traceRuns lay ρ L μ ar M a n (.ok (.ok .fuelExhausted, mt)) ↔
      letI := DialectTrace.stepAt (d := d) lay ρ L
      ∃ body env s₁, f.enter a.toDVals = .ok (body, env) ∧
        Func.traceOps (Step (DialectTrace.Acts d)) M n f env body
          ({ (TraceState.init : TraceState N (unitsOf lay)) with mem := Memories.empty.enter } :
            TraceState N (unitsOf lay))
          (.ok (.ok .fuelExhausted, mt, s₁)) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  constructor
  · rintro ⟨e', he', ho⟩
    rcases e' with ⟨_, _⟩ | ⟨y, t, s'⟩
    · cases ho
    rcases y with _ | (_ | _) <;>
      simp only [Except.map, TraceState.endOf, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and] at ho
    obtain ⟨-, rfl⟩ := ho
    obtain ⟨body, env, hen, e₀, h₀, he₀⟩ :=
      (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).1 he'
    obtain ⟨e₁, h₁, rfl⟩ := (TraceM.run_inFrame _ _ _).1 h₀
    rcases e₁ with ⟨_, _⟩ | ⟨y₁, t₁, s₁⟩
    · cases he₀
    rcases y₁ with _ | (⟨_, _⟩ | _) <;>
      simp only [Except.map, Result.finishEnd, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and] at he₀
    obtain ⟨-, rfl, -⟩ := he₀
    exact ⟨body, env, s₁, hen, h₁⟩
  · rintro ⟨body, env, s₁, hen, h⟩
    exact ⟨_, (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).2
      ⟨body, env, hen, _, (TraceM.run_inFrame _ _ _).2 ⟨_, h, rfl⟩, rfl⟩, rfl⟩

/-- A path of a function's traced runs that runs out of fuel is a path of its
traced runs from the empty memories with nothing escaped that runs out of
fuel after the same marked trace; and each such path is one. -/
theorem Func.traceRuns_exhausted_iff_from {a : HVector toType (f.params.map (·.2))} {n : Nat}
    {mt : List (Step (DialectTrace.Acts d))} :
    f.traceRuns lay ρ L μ ar M a n (.ok (.ok .fuelExhausted, mt)) ↔
      f.traceRunsFrom lay ρ L M (a, TraceState.init) n (.ok (.ok .fuelExhausted, mt)) := by
  constructor
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .ok (.ok .fuelExhausted, _, _), he, ho =>
      cases ho
      exact ⟨_, he, rfl⟩
    | .ok (.ok (.ret _), _, _), _, ho | .ok (.error _, _, _), _, ho | .error _, _, ho => cases ho
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .ok (.ok .fuelExhausted, _, _), he, ho =>
      cases ho
      exact ⟨_, he, rfl⟩
    | .ok (.ok (.ret _), _, _), _, ho | .ok (.error _, _, _), _, ho | .error _, _, ho => cases ho

/-- The traced runs of a function truncate, with at most `W` steps of fuel
between two steps of a path, for any `W` that exceeds the length of every
chain of calls of the module by at least one: its traced runs from the empty
memories do. -/
theorem Func.traceRuns_truncates {W : Nat} (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W)
    (hpos : 0 < W) (a : HVector toType (f.params.map (·.2))) :
    TRun.Truncates W (f.traceRuns lay ρ L μ ar M a) := by
  refine ⟨hpos, fun hle hx => ?_⟩
  obtain ⟨mt, h, hp, ht, hup⟩ := (Func.traceRunsFrom_truncates lay ρ L hW hpos
    (a, TraceState.init)).cut hle ((Func.traceRuns_exhausted_iff_from lay ρ L μ ar).1 hx)
  exact ⟨mt, (Func.traceRuns_exhausted_iff_from lay ρ L μ ar).2 h, hp, ht, hup⟩

/-- The traced runs of a function have finitely many traces at each budget,
given the world's answers, when every op that runs by its own rule has
finitely many outcomes in the traced layer, given the world's answers: its
traced runs from the empty memories do. -/
theorem Func.traceRuns_finitelyMany
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (a : HVector toType (f.params.map (·.2))) :
    TRun.FinitelyMany (f.traceRuns lay ρ L μ ar M a) := fun n ans => by
  obtain ⟨C, hC⟩ := Func.traceRunsFrom_finitelyMany lay ρ L hfin (a, TraceState.init) n ans
  exact ⟨C, fun mt hx hag => hC mt ((Func.traceRuns_exhausted_iff_from lay ρ L μ ar).1 hx) hag⟩

variable [TyRefinement d.Ty] [TyPointers d.Ty] {a a' : HVector toType (f.params.map (·.2))}

/-- Refined arguments over traced runs, for a dialect whose ops show events:
on arguments that refine others, a poison by any value, the traced runs of a
function refine its traced runs on those others, when every terminator and
every op with no callee of the function and of the module's functions is
monotone in the traced layer, every op has finitely many outcomes given the
world's answers, and refinement of values is transitive. -/
theorem Func.traceRuns_isRefinedBy_of_args
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑ traceObservable (f.traceRuns lay ρ L μ ar M a') := by
  obtain ⟨W, hpos, hW⟩ := M.exists_callBound
  have hstep : TRun.ExhaustedAllowed (f.traceRuns lay ρ L μ ar M a) (f.traceRuns lay ρ L μ ar M a') :=
    fun _ _ hx => Func.traceRuns_exhausted_allowed lay ρ L μ ar hmono hf ha hx
  intro t ht
  cases t with
  | ret tr o => exact Func.traceRuns_ret_allowed lay ρ L μ ar htrans hmono hf ha ht
  | ub tr r => exact Func.traceRuns_ub_allowed lay ρ L μ ar hmono hf ha ht
  | diverge tr =>
    exact TRun.diverge_allowed (Func.traceRuns_truncates lay ρ L μ ar hW hpos a)
      (Func.traceRuns_finitelyMany lay ρ L μ ar hfin a) hstep ht
  | reacts T =>
    exact TRun.reacts_allowed (Func.traceRuns_truncates lay ρ L μ ar hW hpos a)
      (Func.traceRuns_finitelyMany lay ρ L μ ar hfin a) hstep ht

end Fir
