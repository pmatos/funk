import Fir.Execution.TraceLift
import Fir.Execution.TraceArgsFrom

/-!
# Traced runs from a traced state, for a dialect that lifts its semantics with memory

A dialect whose traced semantics lifts its semantics with memory onto the
memories of the traced state (`LiftsMem`), as a dialect whose ops show no
event does (`DialectTrace.ofMem`), shows no act on its traced runs. Its
traced runs from a traced state `s` then show no act and let nothing more
escape: they end as its runs from the memories of `s`, each return carrying
the traced state with the memories it ends with and the allocations `s`
lets escape (`Func.traceRunsFrom_noActs`).

So for such a dialect, refinement of runs from given memories gives
refinement of traced runs from given traced states, the traced state each
return ends in included (`Func.traceRunsFrom_isRefinedBy_of_memRunsFrom`).
The core and CoreGpu state congruence in the callee with a hypothesis with
memory; this bridge takes it to the hypothesis that the traced layer's own
theorem asks (`Func.traceRuns_replaceBody_isRefinedBy`). The core has
events, the external calls, but none of its ops shows one, and no run makes
an external call until the run hands a call to a declaration to the core's
external-call rule (#239). So the bridge holds of the core and CoreGpu only
until then; congruence in the callee over traced runs then takes its
hypothesis over traced runs from every traced state (the human's ruling of
2026-11-21 on #239, Q3).
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems)

/-- How a path of a run from the memories of the traced state `s` ends, read
from `s`: a return carries the traced state with the memories it ends with,
and the allocations `s` lets escape. -/
def Result.withEscaped {V : Type} (s : TraceState N (unitsOf lay)) :
    Except Stuck (Result (V × Memories N (unitsOf lay))) →
      Except Stuck (Result (V × TraceState N (unitsOf lay)))
  | .ok (.ret (v, S)) => .ok (.ret (v, { s with mem := S }))
  | .ok .fuelExhausted => .ok .fuelExhausted
  | .error st => .error st

variable {M : Module d} {f : Func d}

/-- The traced runs from a traced state of a function of a dialect whose
traced semantics lifts its semantics with memory show no act, and end as
its runs from the memories of that state, each return carrying the traced
state with the memories it ends with and the allocations that state lets
escape. -/
theorem Func.traceRunsFrom_noActs [DialectTrace d] [LiftsMem d]
    (a : HVector toType (f.params.map (·.2))) (s : TraceState N (unitsOf lay)) (n : Nat) :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    (f.traceRunsFrom lay ρ L M (a, s) n).NoActs
      (Functor.map (f := SetM) (Result.withEscaped lay s) (f.memRunsFrom M (a, s.mem) n)) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  letI := DialectTrace.stepAt (d := d) lay ρ L
  have hlift := LiftsMem.lifts (d := d) lay ρ L
  have hY : TraceM.mapActs Step.acts
      ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) a n).run) =
      TraceM.liftMem (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) a n).run :=
    (congrArg ExceptT.run (Func.run_eraseSteps lay ρ L M f a n)).trans
      (congrArg ExceptT.run (Func.run_map hlift MonadMorphism.traceMem_mapsFrame M f a n)).symm
  have hfwd : ∀ e, ((f.run M (m := TraceM (Step (DialectTrace.Acts d))
        (TraceState N (unitsOf lay))) a n).run s e) →
      TraceM.liftMem (A := DialectTrace.Acts d)
        (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) a n).run s (e.mapActs Step.acts) :=
    fun e h => hY ▸ ⟨e, h, rfl⟩
  have hbwd : ∀ e₀, TraceM.liftMem (A := DialectTrace.Acts d)
      (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) a n).run s e₀ →
      ∃ e, ((f.run M (m := TraceM (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay))) a
        n).run s e) ∧ e₀ = e.mapActs Step.acts := fun e₀ h => (hY ▸ h :)
  have hS : ∀ y, (Functor.map (f := SetM) (Result.withEscaped lay s)
      (f.memRunsFrom M (a, s.mem) n)) y ↔
      (∃ r S', (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) a n).run s.mem
        (.ok (r, S')) ∧ y = .ok (Result.withEscaped lay s (Result.withMem <$> ((·, S') <$> r)))) ∨
        ∃ u, (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) a n).run s.mem (.ub u) ∧
          y = .ub u := by
    intro y
    simp only [Func.memRunsFrom, fromState]
    show (Functor.map (f := SetM) (Result.withEscaped lay s)
      (ExceptT.run (Result.withMem <$> ExceptT.mk _))) y ↔ _
    rw [ExceptT.run_map, ExceptT.run_mk, Functor.map_map, Functor.map_map, SetM.map_iff]
    constructor
    · rintro (⟨⟨r, S'⟩, h, rfl⟩ | ⟨u, h, rfl⟩)
      · exact .inl ⟨r, S', h, rfl⟩
      · exact .inr ⟨u, h, rfl⟩
    · rintro (⟨r, S', h, rfl⟩ | ⟨u, h, rfl⟩)
      · exact .inl ⟨(r, S'), h, rfl⟩
      · exact .inr ⟨u, h, rfl⟩
  have hW : ∀ (r : Except Stuck (Result (List (DVal d)))) (S' : Memories N (unitsOf lay))
      (t : List (Step (DialectTrace.Acts d))),
      TraceEnd.withState (.ok (r, t, { s with mem := S' })) =
        .ok (Result.withEscaped lay s (Result.withMem <$> ((·, S') <$> r)), t) := by
    intro r S' t
    rcases r with _ | (_ | _) <;> rfl
  refine ⟨?_, ?_, fun y => ⟨?_, ?_⟩, fun u => ⟨?_, ?_⟩⟩
  · rintro y mt ⟨(⟨_, _⟩ | ⟨r, t, s₁⟩), he, hy⟩
    · cases hy
    rcases hfwd _ he with ⟨_, S', _, he'⟩ | ⟨_, _, he'⟩
    · simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, ht, rfl⟩ := he'
      rw [hW] at hy
      simp only [Except.ok.injEq, Prod.mk.injEq] at hy
      rw [hy.2]
      exact ht
    · cases he'
  · rintro u mt ⟨(⟨_, t⟩ | ⟨r, t, s₁⟩), he, hy⟩
    · cases hy
      rcases hfwd _ he with ⟨_, _, _, he'⟩ | ⟨_, _, he'⟩
      · cases he'
      · simp only [TraceEnd.mapActs, Except.error.injEq, Prod.mk.injEq] at he'
        exact he'.2
    · rcases r with _ | (_ | _) <;> cases hy
  · rintro ⟨mt, (⟨_, _⟩ | ⟨r, t, s₁⟩), he, hy⟩
    · cases hy
    rcases hfwd _ he with ⟨_, S', hx, he'⟩ | ⟨_, _, he'⟩
    · simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, -, rfl⟩ := he'
      rw [hW] at hy
      simp only [Except.ok.injEq, Prod.mk.injEq] at hy
      exact (hS _).2 (.inl ⟨r, S', hx, by rw [hy.1]⟩)
    · cases he'
  · intro h
    rcases (hS _).1 h with ⟨r, S', hx, hy⟩ | ⟨_, _, hy⟩
    · obtain ⟨(⟨_, _⟩ | ⟨_, t, _⟩), he, he'⟩ := hbwd _ (.inl ⟨r, S', hx, rfl⟩)
      · cases he'
      simp only [TraceEnd.mapActs, Except.ok.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, -, rfl⟩ := he'
      refine ⟨t, _, he, ?_⟩
      rw [hW]
      cases hy
      rfl
    · cases hy
  · rintro ⟨mt, (⟨u', t⟩ | ⟨r, t, s₁⟩), he, hy⟩
    · cases hy
      rcases hfwd _ he with ⟨_, _, _, he'⟩ | ⟨_, hx, he'⟩
      · cases he'
      simp only [TraceEnd.mapActs, Except.error.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      exact (hS _).2 (.inr ⟨_, hx, rfl⟩)
    · rcases r with _ | (_ | _) <;> cases hy
  · intro h
    rcases (hS _).1 h with ⟨_, _, _, hy⟩ | ⟨u', hx, hy⟩
    · cases hy
    cases hy
    obtain ⟨(⟨_, t⟩ | ⟨_, _, _⟩), he, he'⟩ := hbwd _ (.inr ⟨_, hx, rfl⟩)
    · simp only [TraceEnd.mapActs, Except.error.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      exact ⟨t, _, he, rfl⟩
    · cases he'

omit [DecidableEq N] in
/-- A run from the memories of a traced state, read from that state, returns
with a traced state exactly when the run returns with its memories, and that
traced state is the first with those memories. -/
theorem Result.withEscaped_ret_iff {V : Type} {s : TraceState N (unitsOf lay)}
    {R : Run (V × Memories N (unitsOf lay))} {v : V} {s₁ : TraceState N (unitsOf lay)} :
    Run.outcomes (Functor.map (f := SetM) (Result.withEscaped lay s) R) (.ret (v, s₁)) ↔
      ∃ S, s₁ = { s with mem := S } ∧ R.outcomes (.ret (v, S)) := by
  simp only [Run.outcomes, SetM.map_iff]
  constructor
  · rintro (⟨x, hx, he⟩ | ⟨_, _, he⟩)
    · rcases x with _ | (⟨_, S⟩ | _) <;> cases he
      exact ⟨S, rfl, hx⟩
    · cases he
  · rintro ⟨S, rfl, h⟩
    exact .inl ⟨_, h, rfl⟩

omit [DecidableEq N] in
/-- A run from the memories of a traced state, read from that state, hits UB
exactly when the run does. -/
theorem Result.withEscaped_ub_iff {V : Type} {s : TraceState N (unitsOf lay)}
    {R : Run (V × Memories N (unitsOf lay))} {r : String} :
    Run.outcomes (Functor.map (f := SetM) (Result.withEscaped lay s) R) (.ub r) ↔ R.outcomes (.ub r) := by
  simp only [Run.outcomes, SetM.map_iff]
  constructor
  · rintro (⟨_, _, he⟩ | ⟨_, h, he⟩) <;> cases he
    exact h
  · exact fun h => .inr ⟨r, h, rfl⟩

omit [DecidableEq N] in
/-- A run from the memories of a traced state, read from that state, runs out
of fuel exactly when the run does. -/
theorem Result.withEscaped_exhausted_iff {V : Type} {s : TraceState N (unitsOf lay)}
    {R : Run (V × Memories N (unitsOf lay))} :
    Run.outcomes (Functor.map (f := SetM) (Result.withEscaped lay s) R) .fuelExhausted ↔
      R.outcomes .fuelExhausted := by
  simp only [Run.outcomes, SetM.map_iff]
  constructor
  · rintro (⟨x, hx, he⟩ | ⟨_, _, he⟩)
    · rcases x with _ | (_ | _) <;> cases he
      exact hx
    · cases he
  · exact fun h => .inl ⟨_, h, rfl⟩

variable [TyRefinement d.Ty]

/-- Refinement of runs from the memories of a traced state gives refinement of
traced runs from that state, for a dialect whose traced semantics lifts its
semantics with memory: the traced state each return ends in included. -/
theorem Func.traceRunsFrom_isRefinedBy_of_memRunsFrom [DialectTrace d] [LiftsMem d]
    {M' : Module d} {f' : Func d}
    {a : HVector toType (f.params.map (·.2))} {a' : HVector toType (f'.params.map (·.2))}
    {s : TraceState N (unitsOf lay)}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      observable (f.memRunsFrom M (a, s.mem)) ⊑ observable (f'.memRunsFrom M' (a', s.mem))) :
    traceObservable (f.traceRunsFrom lay ρ L M (a, s)) ⊑
      traceObservable (f'.traceRunsFrom lay ρ L M' (a', s)) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  rw [traceObservable_of_noActs (Func.traceRunsFrom_noActs lay ρ L a s),
    traceObservable_of_noActs (Func.traceRunsFrom_noActs lay ρ L a' s)]
  refine TBehaviour.ofBehaviour_isRefinedBy_iff.2 fun t ht => ?_
  have hub : ∀ {r : String}, observable (f.memRunsFrom M (a, s.mem)) (.ub r) →
      observable (fun n => Functor.map (f := SetM) (Result.withEscaped lay s)
        (f.memRunsFrom M (a, s.mem) n)) (.ub r) :=
    fun ⟨m, hm⟩ => ⟨m, Result.withEscaped_ub_iff lay (s := s) |>.2 hm⟩
  match t, ht with
  | .ret (v', s₁), ⟨n, hn⟩ =>
    obtain ⟨S', rfl, hn'⟩ := (Result.withEscaped_ret_iff lay (s := s)).1 hn
    obtain ⟨o, ho, hle⟩ := h (.ret (v', S')) ⟨n, hn'⟩
    match o, ho, hle with
    | .ub _, ho, _ => exact ⟨_, hub ho, trivial⟩
    | .ret (v, S), ⟨m, hm⟩, hle =>
      exact ⟨.ret (v, { s with mem := S }), ⟨m, (Result.withEscaped_ret_iff lay (s := s)).2 ⟨S, rfl, hm⟩⟩,
        hle.1, hle.2, rfl⟩
  | .ub r, ⟨n, hn⟩ =>
    obtain ⟨o, ho, hle⟩ := h (.ub r) ⟨n, (Result.withEscaped_ub_iff lay (s := s)).1 hn⟩
    match o, ho, hle with
    | .ub _, ho, _ => exact ⟨_, hub ho, trivial⟩
  | .fuelExhausted, ht =>
    obtain ⟨o, ho, hle⟩ :=
      h .fuelExhausted fun n => (Result.withEscaped_exhausted_iff lay (s := s)).1 (ht n)
    match o, ho, hle with
    | .ub _, ho, _ => exact ⟨_, hub ho, trivial⟩
    | .fuelExhausted, ho, _ =>
      exact ⟨.fuelExhausted, fun n => (Result.withEscaped_exhausted_iff lay (s := s)).2 (ho n), trivial⟩

end Fir
