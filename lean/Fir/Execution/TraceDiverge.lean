import Fir.Execution.TraceKonig
import Fir.Execution.TraceTruncate
import Fir.Execution.TraceFiniteRuns

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
human's ruling of 2026-11-20, on #233), the traced runs of a function on
arguments that refine others, a poison by any value, refine its traced runs
on those others: returns, UB, silent divergence and acts forever.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectTrace d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule) {M : Module d}
  {f : Func d}

/-- The traced runs of a function truncate, with at most `W` steps of fuel
between two steps of a path, for any `W` that exceeds the length of every
chain of calls of the module by at least one. -/
theorem Func.traceRuns_truncates {W : Nat} (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W)
    (hpos : 0 < W) (a : HVector toType (f.params.map (·.2))) :
    TRun.Truncates W (f.traceRuns lay ρ L μ ar M a) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  refine ⟨hpos, fun {n n' mt'} hle hx => ?_⟩
  obtain ⟨e', he', ho⟩ := hx
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
  rw [← Nat.add_sub_cancel' hle] at h₁
  obtain ⟨e, h, t₀, s₀, rfl, hp, ht₀, hb⟩ := Func.traceOps_cut _ (DialectTrace.stepAt_oneStep lay ρ L)
    hW hpos n (n' - n) _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
  refine ⟨t₀, ⟨_, (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).2
    ⟨body, env, hen, _, (TraceM.run_inFrame _ _ _).2 ⟨_, h, rfl⟩, rfl⟩, rfl⟩, hp, ht₀, fun K hK => ?_⟩
  rcases hb with rfl | ⟨c, hc, hn⟩
  · rfl
  obtain ⟨r, rfl⟩ := hp
  have := hW _ _ hc
  have hlt : W * (K + 1) < W * (Step.ticks t₀ + 1) := by
    have : W * (Step.ticks t₀ + 1) = W * Step.ticks t₀ + W := Nat.mul_succ _ _
    omega
  have hK' : K < Step.ticks t₀ := by have := Nat.lt_of_mul_lt_mul_left hlt; omega
  exact (Step.upTo_append_of_lt (mt := t₀) r hK').symm

/-- The traced runs of a function have finitely many traces at each budget,
given the world's answers, when every op that runs by its own rule has
finitely many outcomes in the traced layer, given the world's answers. -/
theorem Func.traceRuns_finitelyMany
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (a : HVector toType (f.params.map (·.2))) :
    TRun.FinitelyMany (f.traceRuns lay ρ L μ ar M a) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  intro n ans
  cases hen : f.enter a.toDVals with
  | error _ =>
    refine ⟨[], fun mt hx _ => ?_⟩
    obtain ⟨e', he', ho⟩ := hx
    rcases e' with ⟨_, _⟩ | ⟨y, t, s'⟩
    · cases ho
    rcases y with _ | (_ | _) <;>
      simp only [Except.map, TraceState.endOf, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and] at ho
    obtain ⟨_, _, hen', -⟩ := (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).1 he'
    rw [hen] at hen'
    cases hen'
  | ok p =>
    obtain ⟨C, hC⟩ := Func.traceOps_finite (OpsTraceFinite.stepAt lay ρ L hfin) M n f p.2 p.1
      { (TraceState.init : TraceState N (unitsOf lay)) with mem := Memories.empty.enter } ans
    refine ⟨C.map (·.2.1), fun mt hx hag => ?_⟩
    obtain ⟨e', he', ho⟩ := hx
    rcases e' with ⟨_, _⟩ | ⟨y, t, s'⟩
    · cases ho
    rcases y with _ | (_ | _) <;>
      simp only [Except.map, TraceState.endOf, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and] at ho
    obtain ⟨-, rfl⟩ := ho
    obtain ⟨body, env, hen', e₀, h₀, he₀⟩ :=
      (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).1 he'
    rw [hen] at hen'
    cases hen'
    obtain ⟨e₁, h₁, rfl⟩ := (TraceM.run_inFrame _ _ _).1 h₀
    rcases e₁ with ⟨_, _⟩ | ⟨y₁, t₁, s₁⟩
    · cases he₀
    rcases y₁ with _ | (⟨_, _⟩ | _) <;>
      simp only [Except.map, Result.finishEnd, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and] at he₀
    obtain ⟨-, rfl, -⟩ := he₀
    exact List.mem_map.2 ⟨_, hC _ _ _ h₁ hag, rfl⟩

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
