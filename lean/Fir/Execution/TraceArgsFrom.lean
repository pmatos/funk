import Fir.Execution.TraceBlackBox
import Fir.Execution.TraceKonig
import Fir.Execution.TraceTruncate
import Fir.Execution.TraceFiniteRuns

/-!
# Refined arguments over traced runs from a given traced state

A callee runs from the traced state its caller reached. So congruence in the
callee asks of a function's traced runs _from a traced state_, which return
its values with the traced state they end in (`Func.traceRunsFrom`), what
refined arguments give of its traced runs from the memories a run starts
with: on arguments that refine others, a poison by any value, and from a
traced state that refines another, its traced runs refine its traced runs on those others
from that other state, the traced state each return ends in included.

The proof is the one for the traced runs from the memories a run starts
with, from any traced state; those runs (`Fir.Execution.TraceDiverge`) are
these from one traced state and take their truncation and finiteness from here. The two
runs go in step (`Func.traceRun_allowed` starts from any traced states that
refine each other). Each return and UB of the target's is allowed by one of the
source's; at each budget, each path of the target's that runs out of fuel is
allowed by one of the source's. The source's traced runs from a traced state
truncate, and have finitely many traces at each budget when every op and
every external call has finitely many outcomes given the world's answers, so König's lemma
(`Fir.Execution.TraceKonig`) gives divergence, silent and with acts forever.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectTrace d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) {M : Module d} {f : Func d}

/-- The traced runs of the function `f` of the module `M` from given traced
states, where a run names the dialect's memory `x` as `ρ x`, whose layout
entry is `lay (ρ x)`, and gives each op the items `L`: on each argument
vector and from each traced state, its run in the traced layer of marked
traces, each op that runs by the dialect's rule showing a step before it,
at each budget, which returns its values with the traced state it ends
in. -/
def Func.traceRunsFrom (M : Module d) (f : Func d) :
    FuncTraceRuns (HVector toType (f.params.map (·.2)) × TraceState N (unitsOf lay))
      (DialectTrace.Acts d) (List (DVal d) × TraceState N (unitsOf lay)) :=
  letI := DialectTrace.stepAt (d := d) lay ρ L
  f.traceFrom M

/-- A function's traced runs from a traced state truncate, with at most `W`
steps of fuel between two steps of a path, for any `W` that exceeds the
length of every chain of calls of the module by at least one. -/
theorem Func.traceRunsFrom_truncates {W : Nat} (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W)
    (hpos : 0 < W) (p : HVector toType (f.params.map (·.2)) × TraceState N (unitsOf lay)) :
    TRun.Truncates W (f.traceRunsFrom lay ρ L M p) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  obtain ⟨a, s⟩ := p
  refine ⟨hpos, fun {n n' mt'} hle hx => ?_⟩
  obtain ⟨body, env, s₁, hen, h₁⟩ := Func.traceFrom_exhausted_iff.1 hx
  obtain ⟨e₁, h₁', he₁⟩ := (TraceM.run_inFrame _ _ _).1 h₁
  match e₁, h₁', he₁ with
  | .ok (.ok .fuelExhausted, _, _), h₁', he₁ =>
    cases he₁
    rw [← Nat.add_sub_cancel' hle] at h₁'
    obtain ⟨e, h, t₀, s₀, rfl, hp, ht₀, hb⟩ := Func.traceOps_cut _
      (DialectTrace.stepAt_oneStep lay ρ L) hW hpos n (n' - n) _ _ _ _ _ h₁'
      (TraceEnd.notStuck_ok _ _ _)
    refine ⟨t₀, Func.traceFrom_exhausted_iff.2 ⟨body, env, _, hen,
      (TraceM.run_inFrame _ _ _).2 ⟨_, h, rfl⟩⟩, hp, ht₀, fun K hK => ?_⟩
    rcases hb with rfl | ⟨c, hc, hn⟩
    · rfl
    obtain ⟨r, rfl⟩ := hp
    have := hW _ _ hc
    have hlt : W * (K + 1) < W * (Step.ticks t₀ + 1) := by
      have : W * (Step.ticks t₀ + 1) = W * Step.ticks t₀ + W := Nat.mul_succ _ _
      omega
    have hK' : K < Step.ticks t₀ := by have := Nat.lt_of_mul_lt_mul_left hlt; omega
    exact (Step.upTo_append_of_lt (mt := t₀) r hK').symm
  | .ok (.ok (.ret _), _, _), _, he₁ | .ok (.error _, _, _), _, he₁ | .error _, _, he₁ =>
    cases he₁

/-- A function's traced runs from a traced state have finitely many traces
at each budget, given the world's answers, when every op that runs by its
own rule has finitely many outcomes in the traced layer, given the world's
answers. -/
theorem Func.traceRunsFrom_finitelyMany
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (p : HVector toType (f.params.map (·.2)) × TraceState N (unitsOf lay)) :
    TRun.FinitelyMany (f.traceRunsFrom lay ρ L M p) := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  obtain ⟨a, s⟩ := p
  intro n ans
  cases hen : f.enter a.toDVals with
  | error _ =>
    refine ⟨[], fun mt hx _ => ?_⟩
    obtain ⟨_, _, _, hen', -⟩ := Func.traceFrom_exhausted_iff.1 hx
    rw [hen] at hen'
    cases hen'
  | ok q =>
    obtain ⟨C, hC⟩ := Func.traceOps_finite (OpsTraceFinite.stepAt lay ρ L hfin) M n f q.2 q.1
      { s with mem := s.mem.enter } ans
    refine ⟨C.map (·.2.1), fun mt hx hag => ?_⟩
    obtain ⟨_, _, _, hen', h₁⟩ := Func.traceFrom_exhausted_iff.1 hx
    rw [hen] at hen'
    cases hen'
    obtain ⟨e₁, h₁', he₁⟩ := (TraceM.run_inFrame _ _ _).1 h₁
    match e₁, h₁', he₁ with
    | .ok (.ok .fuelExhausted, _, _), h₁', he₁ =>
      cases he₁
      exact List.mem_map.2 ⟨_, hC _ _ _ h₁' hag, rfl⟩
    | .ok (.ok (.ret _), _, _), _, he₁ | .ok (.error _, _, _), _, he₁ | .error _, _, he₁ =>
      cases he₁

variable [TyRefinement d.Ty]
  {a a' : HVector toType (f.params.map (·.2))} {s s' : TraceState N (unitsOf lay)}

/-- At every budget, every path of a function's traced runs from a traced
state, on arguments that refine others, that is not stuck is allowed in step
by a path of its traced runs from a traced state that it refines, on those
others, when every terminator and every op with no callee of the function and
of the module's functions is monotone in the traced layer. -/
theorem Func.traceRunsFrom_path_allowed
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') (hs : s ⊑ s') {n : Nat}
    {o : Except (String × List (Step (DialectTrace.Acts d)))
      (Except Stuck (Result (List (DVal d) × TraceState N (unitsOf lay))) ×
        List (Step (DialectTrace.Acts d)))}
    (hx : f.traceRunsFrom lay ρ L M (a', s') n o) (hne : ∀ st mt, o ≠ .ok (.error st, mt)) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    ∃ e e', (f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) a n).run
        s e ∧ o = TraceEnd.withState e' ∧ TraceEnd.Allows Result.Finished e e' := by
  letI := DialectTrace.stepAt (d := d) lay ρ L
  obtain ⟨e', he', rfl⟩ := hx
  have hne' : TraceEnd.NotStuck e' := by
    rintro st t s₁ rfl
    exact hne st t rfl
  obtain ⟨e, he, hle⟩ := Func.traceRun_allowed
    (fun g hg => Func.TraceOpsMonotone.stepAt lay ρ L (hmono g hg))
    (Func.TraceOpsMonotone.stepAt lay ρ L hf) ha hs n he' hne'
  exact ⟨e, e', he, rfl, hle⟩

/-- Refined arguments over traced runs from a given traced state, for a
dialect whose ops show events: on arguments that refine others, a poison by
any value, and from a traced state that refines another, the traced runs of
a function refine its traced runs on those others from that other state,
the traced state each return ends in included, when every terminator and
every op with no callee of the function and of the module's functions is
monotone in the traced layer and every op has finitely many outcomes given
the world's answers. -/
theorem Func.traceRunsFrom_isRefinedBy_of_args
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') (hs : s ⊑ s') :
    traceObservable (f.traceRunsFrom lay ρ L M (a, s)) ⊑
      traceObservable (f.traceRunsFrom lay ρ L M (a', s')) := by
  obtain ⟨W, hpos, hW⟩ := M.exists_callBound
  have hpath := fun {n o} hx hne =>
    Func.traceRunsFrom_path_allowed lay ρ L (n := n) (o := o) hmono hf ha hs hx hne
  have hstep : TRun.ExhaustedAllowed (f.traceRunsFrom lay ρ L M (a, s))
      (f.traceRunsFrom lay ρ L M (a', s')) := fun n mt' hx => by
    obtain ⟨e, e', he, ho, hle⟩ := hpath hx (fun _ _ h => by cases h)
    match e', ho, e, he, hle with
    | .ok (.ok .fuelExhausted, _, _), ho, .error (r, t), he, hle =>
      cases ho
      exact .inr ⟨r, t, ⟨_, he, rfl⟩, hle⟩
    | .ok (.ok .fuelExhausted, _, _), ho, .ok (.ok .fuelExhausted, t, _), he, hle =>
      cases ho
      exact .inl ⟨t, ⟨_, he, rfl⟩, hle.2.1⟩
    | .ok (.ok .fuelExhausted, _, _), _, .ok (.ok (.ret _), _, _), _, hle
    | .ok (.ok .fuelExhausted, _, _), _, .ok (.error _, _, _), _, hle => exact hle.1.elim
    | .ok (.ok (.ret _), _, _), ho, _, _, _ | .ok (.error _, _, _), ho, _, _, _
    | .error _, ho, _, _, _ => cases ho
  intro t ht
  cases t with
  | ret tr o' =>
    obtain ⟨n, mt', hx, rfl⟩ := ht
    obtain ⟨e, e', he, ho, hle⟩ := hpath hx (fun _ _ h => by cases h)
    match e', ho, e, he, hle with
    | .ok (.ok (.ret _), _, _), ho, .error (r, t), he, hle =>
      cases ho
      exact ⟨.ub (Step.actsOf t) r, ⟨n, t, ⟨_, he, rfl⟩, rfl⟩,
        (Step.actsOf_isRefinedPrefix hle).getElem?⟩
    | .ok (.ok (.ret _), _, _), ho, .ok (.ok (.ret vs), t, s₁), he, hle =>
      cases ho
      exact ⟨.ret (Step.actsOf t) (vs, s₁), ⟨n, t, ⟨_, he, rfl⟩, rfl⟩,
        Step.actsOf_isRefinedBy hle.2.1, hle.1, hle.2.2⟩
    | .ok (.ok (.ret _), _, _), _, .ok (.ok .fuelExhausted, _, _), _, hle
    | .ok (.ok (.ret _), _, _), _, .ok (.error _, _, _), _, hle => exact hle.1.elim
    | .ok (.ok .fuelExhausted, _, _), ho, _, _, _ | .ok (.error _, _, _), ho, _, _, _
    | .error _, ho, _, _, _ => cases ho
  | ub tr r' =>
    obtain ⟨n, mt', hx, rfl⟩ := ht
    obtain ⟨e, e', he, ho, hle⟩ := hpath hx (fun _ _ h => by cases h)
    match e', ho, e, he, hle with
    | .error _, ho, .error (r, t), he, hle =>
      cases ho
      exact ⟨.ub (Step.actsOf t) r, ⟨n, t, ⟨_, he, rfl⟩, rfl⟩,
        (Step.actsOf_isRefinedPrefix hle).getElem?⟩
    | .error _, _, .ok _, _, hle => exact hle.elim
    | .ok (.ok (.ret _), _, _), ho, _, _, _ | .ok (.ok .fuelExhausted, _, _), ho, _, _, _
    | .ok (.error _, _, _), ho, _, _, _ => cases ho
  | diverge tr =>
    exact TRun.diverge_allowed (Func.traceRunsFrom_truncates lay ρ L hW hpos _)
      (Func.traceRunsFrom_finitelyMany lay ρ L hfin _) hstep ht
  | reacts T =>
    exact TRun.reacts_allowed (Func.traceRunsFrom_truncates lay ρ L hW hpos _)
      (Func.traceRunsFrom_finitelyMany lay ρ L hfin _) hstep ht

end Fir
