import FirTest.TraceCallDialect

/-!
The callee of the tests of divergence across a replaced callee (stage 3c-2 of
#233): `@g` of `FirTest.TraceCallDialect`, which takes a step to `skip`, then
returns, is refined by its new body, which returns at once, one step fewer.
From every traced state, the new `@g` only returns, with no value, in the
traced state it started from, after no act; the old one returns the same at
the budget `2`.
-/

namespace FirTest.TraceCalleeRefine

open Fir Fir.Memory FirTest.TraceDialect FirTest.TraceCallDialect

/-- The traced semantics of the call dialect in the traced layer of marked
traces. -/
abbrev stepSem := DialectTrace.stepAt (d := CallDialect) lay Empty.elim RunItems.empty

/-- The new `@g`. -/
abbrev g' : Func CallDialect := g.replaceBody g.name newBody

/-- An op whose rule ends with a value at once ends, in the traced layer of
marked traces, with that value after its step. -/
theorem step_pure {α : Type} (a : α) (s : St)
    (e : TraceEnd (Step (DialectTrace.Acts CallDialect)) St α) :
    (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [Step.act a])
      (pure a : TraceM (DialectTrace.Acts CallDialect) St α)) s e ↔ e = .ok (a, [.tick], s) := by
  rw [TraceM.bind_apply]
  constructor
  · rintro (⟨_, t, s₁, e₁, ht, ⟨e₀, h₀, rfl⟩, rfl⟩ | ⟨_, _, ht, _⟩)
    · have ht : (Except.ok ((), t, s₁) : TraceEnd (Step (DialectTrace.Acts CallDialect)) St Unit) =
          .ok ((), [.tick], s) := ht
      cases ht
      have h₀ : e₀ = .ok (a, [], s) := h₀
      subst h₀
      rfl
    · cases ht
  · rintro rfl
    exact .inl ⟨(), [.tick], s, _, rfl, ⟨_, rfl, rfl⟩, rfl⟩

/-- `emit` ends, in the traced layer of marked traces, after its step and the
act of the event `0` with any answer. -/
theorem step_emit (args : HVector toType (sig (d := CallDialect) CallOp.emit)) (s : St)
    (n : Nat) :
    stepSem.denote CallOp.emit args s (.ok (.nil, [.tick, .act ⟨(0 : Nat), n⟩], s)) :=
  (TraceM.bind_apply _ _ _ _).2 (.inl ⟨(), [.tick], s, _, rfl,
    ⟨.ok (.nil, [⟨(0 : Nat), n⟩], s), (emit_iff args s _).2 ⟨n, rfl⟩, rfl⟩, rfl⟩)

/-- The new `@g` enters its one block, which returns. -/
theorem g'_enter : g'.enter (HVector.nil : HVector toType ([] : List Core.Ty)).toDVals =
    .ok ([mkOp .ret], []) := rfl

/-- The old `@g` enters its one block. -/
theorem g_enter : g.enter (HVector.nil : HVector toType ([] : List Core.Ty)).toDVals =
    .ok ([mkOp .skip, mkOp .ret], []) := rfl

/-- The block of the new `@g`, from any traced state, returns at every budget
of at least one, after one step, with no value, in that traced state, and
runs out of fuel at the budget `0`, and only so. -/
theorem retOps_iff {M : Module CallDialect} {f : Func CallDialect} (hres : f.results = [])
    {n : Nat} {s : St}
    {e : TraceEnd (Step (DialectTrace.Acts CallDialect)) St
      (Except Stuck (Result (List (DVal CallDialect) × Nat)))} (hne : TraceEnd.NotStuck e) :
    letI := stepSem
    Func.traceOps (Step (DialectTrace.Acts CallDialect)) M n f [] [mkOp .ret] s e ↔
      (n = 0 ∧ e = .ok (.ok .fuelExhausted, [], s)) ∨
        ∃ m, n = m + 1 ∧ e = .ok (.ok (.ret ([], m)), [.tick], s) := by
  letI := stepSem
  constructor
  · intro h
    match n, h with
    | 0, h => exact .inl ⟨rfl, Func.traceOps_zero.1 h⟩
    | m + 1, h =>
      refine .inr ⟨m, rfl, ?_⟩
      cases (Func.tStepPath_iff hne).1 h with
      | exitUB _ _ _ _ hx => cases (step_pure _ _ _).1 hx
      | ret _ hargs _ _ hx =>
        cases hargs
        cases (step_pure _ _ _).1 hx
        rfl
      | goto _ _ _ _ hx => cases (step_pure _ _ _).1 hx
      | denoteUB _ _ hT => cases hT
      | denote _ _ hT => cases hT
      | callUB _ _ hT => cases hT
      | callExh _ _ hT => cases hT
      | callRet _ _ hT => cases hT
      | extUB _ _ hT => cases hT
      | ext _ _ hT => cases hT
  · rintro (⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩)
    · exact Func.traceOps_zero.2 rfl
    · exact (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
        (.ret (args := .nil) rfl rfl rfl rfl ((step_pure _ _ _).2 rfl) (by rw [hres]; rfl))

/-- The old `@g` returns at the budget `2` from every traced state, after its
two steps, with no value, in that traced state. -/
theorem g_ret (s : St) :
    g.traceRunsFrom lay Empty.elim RunItems.empty callModule (.nil, s) 2
      (.ok (.ok (.ret ([], s)),
        ([.tick, .tick] : List (Step (DialectTrace.Acts CallDialect))))) := by
  letI := stepSem
  have hret := (retOps_iff (M := callModule) (f := g) rfl (n := 1)
    (s := { s with mem := s.mem.enter }) (TraceEnd.notStuck_ok _ _ _)).2 (.inr ⟨0, rfl, rfl⟩)
  have hops : Func.traceOps (Step (DialectTrace.Acts CallDialect)) callModule 2 g []
      [mkOp .skip, mkOp .ret] { s with mem := s.mem.enter }
      (.ok (.ok (.ret ([], 0)), [.tick, .tick], { s with mem := s.mem.enter })) :=
    (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
      (.denote (args := .nil) (rs := .nil) (t := [Step.tick]) (s' := { s with mem := s.mem.enter })
        (e := .ok (.ok (.ret ([], 0)), [Step.tick], { s with mem := s.mem.enter })) rfl rfl rfl rfl
        ((step_pure _ _ _).2 rfl) rfl hret)
  refine Func.traceFrom_ret_iff.2 ⟨_, _, g_enter, 0, ?_⟩
  exact (TraceM.run_inFrame _ _ _).2 ⟨_, hops, by cases s; rfl⟩

/-- The new `@g`'s block in its frame, from any traced state, returns after one
step, with no value, in that traced state, or runs out of fuel at the budget
`0`, and only so. -/
theorem g'_call {n : Nat} {s : St}
    {e : TraceEnd (Step (DialectTrace.Acts CallDialect)) St
      (Except Stuck (Result (List (DVal CallDialect) × Nat)))} (hne : TraceEnd.NotStuck e)
    (h : letI := stepSem
      Func.traceCall (Step (DialectTrace.Acts CallDialect)) newModule n g' [] [mkOp .ret] s e) :
    (n = 0 ∧ ∃ s₁, e = .ok (.ok .fuelExhausted, [], s₁)) ∨
      ∃ m, n = m + 1 ∧ e = .ok (.ok (.ret ([], m)), [.tick], s) := by
  letI := stepSem
  obtain ⟨e₁, h₁, rfl⟩ := (TraceM.run_inFrame _ _ _).1 h
  have hne₁ : TraceEnd.NotStuck e₁ := by
    rintro st t s₁ rfl
    exact hne st t _ rfl
  rcases (retOps_iff rfl hne₁).1 h₁ with ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · exact .inl ⟨rfl, _, rfl⟩
  · exact .inr ⟨m, rfl, by cases s; rfl⟩

/-- The old `@g` is refined by the new one, from every traced state: the new
one only returns, with no value, in the traced state it started from, after
no act, as the old one does at the budget `2`. -/
theorem g_isRefinedBy :
    g.traceRunsFrom lay Empty.elim RunItems.empty callModule ⊑
      g'.traceRunsFrom lay Empty.elim RunItems.empty newModule := by
  letI := stepSem
  rintro ⟨a, s⟩ t' ht'
  cases a
  have noExh : ∀ {mt : List (Step (DialectTrace.Acts CallDialect))},
      ¬ g'.traceRunsFrom lay Empty.elim RunItems.empty newModule (.nil, s) 1
        (.ok (.ok .fuelExhausted, mt)) := fun hx => by
    obtain ⟨body, env, s₁, hen, h₁⟩ := Func.traceFrom_exhausted_iff.1 hx
    have hen := hen.symm.trans g'_enter
    simp only [Except.ok.injEq, Prod.mk.injEq] at hen
    obtain ⟨rfl, rfl⟩ := hen
    rcases g'_call (TraceEnd.notStuck_ok _ _ _) h₁ with ⟨h, -⟩ | ⟨_, -, h⟩ <;> cases h
  cases t' with
  | ret tr o =>
    obtain ⟨n, mt, hx, rfl⟩ := ht'
    obtain ⟨vs, s₁⟩ := o
    obtain ⟨body, env, hen, k, h₁⟩ := Func.traceFrom_ret_iff.1 hx
    have hen := hen.symm.trans g'_enter
    simp only [Except.ok.injEq, Prod.mk.injEq] at hen
    obtain ⟨rfl, rfl⟩ := hen
    rcases g'_call (TraceEnd.notStuck_ok _ _ _) h₁ with ⟨-, _, h⟩ | ⟨_, -, h⟩
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq, Result.ret.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := h
    exact ⟨.ret [] ([], s₁), ⟨2, _, g_ret s₁, rfl⟩, trivial, trivial,
      TraceState.isRefinedBy_refl s₁⟩
  | ub tr r =>
    obtain ⟨n, mt, hx, rfl⟩ := ht'
    obtain ⟨body, env, hen, h₁⟩ := Func.traceFrom_ub_iff.1 hx
    have hen := hen.symm.trans g'_enter
    simp only [Except.ok.injEq, Prod.mk.injEq] at hen
    obtain ⟨rfl, rfl⟩ := hen
    rcases g'_call (TraceEnd.notStuck_error _ _) h₁ with ⟨-, _, h⟩ | ⟨_, -, h⟩ <;> cases h
  | diverge tr =>
    obtain ⟨N, hN⟩ := ht'
    obtain ⟨mt, hmt, -⟩ := hN 1
    exact (noExh hmt).elim
  | reacts T =>
    obtain ⟨K, hK⟩ := ht'
    obtain ⟨mt, hmt, -⟩ := hK 1
    exact (noExh hmt).elim

end FirTest.TraceCalleeRefine
