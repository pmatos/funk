import Fir.Execution.TraceTruncate

/-!
# A callee's return, cut and paced

A callee's return in its frame, in the traced layer of marked traces, when
every path of every op shows one step: it leaves at least as many steps as
its marked trace and shows a step (`Func.traceCall_retPaced`); it takes at
most `W` steps of fuel for each of its steps (`Func.traceCall_retPaced_le`);
and cut to a smaller budget it returns with as many fewer steps left, or
runs out of fuel truncated (`Func.traceCall_cut_ret`). The moves of
`Fir.Execution.TraceMoves` use them for a call whose callee returns.
-/

namespace Fir

open Memory

variable {A : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M : Module d}

/-- A return of a callee's ops in its frame leaves at least as many steps as
its marked trace, and shows a step, when every path of every op shows exactly
one step. -/
theorem Func.traceCall_retPaced (hone : OpsOneStep d A (TraceState Mem unit)) {U k : Nat}
    {g : Func d} {genv : Env d} {body : List (Operation d)} {s s₁ : TraceState Mem unit}
    {vs : List (DVal d)} {t : List (Step A)}
    (h : Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁))) :
    k + Step.ticks t ≤ U ∧ 0 < Step.ticks t := by
  obtain ⟨W, -, hW⟩ := M.exists_callBound
  obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 h
  rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
  · cases he₁
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
  obtain ⟨rfl, rfl, -⟩ := he₁
  obtain ⟨hk, hp, -⟩ := Func.traceOps_retPaced A hone hW U _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
  exact ⟨hk, hp⟩

/-- A return of a callee's ops in its frame takes at most `W` steps of fuel for
each of its steps, when `W` exceeds the length of every chain of calls of the
module by at least one. -/
theorem Func.traceCall_retPaced_le (hone : OpsOneStep d A (TraceState Mem unit)) {W : Nat}
    (hW : ∀ os c, M.CallChain os c → c + 2 ≤ W) {U k : Nat} {g : Func d} {genv : Env d}
    {body : List (Operation d)} {s s₁ : TraceState Mem unit} {vs : List (DVal d)}
    {t : List (Step A)}
    (h : Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁))) :
    U ≤ k + W * Step.ticks t := by
  obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 h
  rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
  · cases he₁
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
  obtain ⟨rfl, rfl, -⟩ := he₁
  obtain ⟨-, -, c, hc, hb⟩ :=
    Func.traceOps_retPaced A hone hW U _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
  have := hW _ _ hc
  omega

/-- A return of a callee's ops in its frame at the budget `U`, cut to a smaller
budget `n`, returns there with as many fewer steps left, when it left at least
`U - n`; otherwise the callee runs out of fuel at `n`, truncated: after a
marked trace that starts its own, of at most `n` steps, that is all of its own
or has `n ≤ W m + c`, for its `m` steps and a chain of `c` calls. -/
theorem Func.traceCall_cut_ret (hone : OpsOneStep d A (TraceState Mem unit)) {W : Nat}
    (hW : ∀ os c, M.CallChain os c → c + 2 ≤ W) (hpos : 0 < W) {U n k : Nat}
    (hn : n ≤ U) {g : Func d} {genv : Env d} {body : List (Operation d)} {s s₁ : TraceState Mem unit}
    {vs : List (DVal d)} {t : List (Step A)}
    (h : Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁))) :
    (U - n ≤ k ∧
      Func.traceCall (Step A) M n g genv body s (.ok (.ok (.ret (vs, k - (U - n))), t, s₁))) ∨
    (k < U - n ∧ ∃ t₀ s₀, t₀ <+: t ∧ Step.ticks t₀ ≤ n ∧
      (t₀ = t ∨ ∃ c, M.CallChain body c ∧ n ≤ W * Step.ticks t₀ + c) ∧
      Func.traceCall (Step A) M n g genv body s (.ok (.ok .fuelExhausted, t₀, s₀))) := by
  obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 h
  rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
  · cases he₁
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
  obtain ⟨rfl, rfl, rfl⟩ := he₁
  rw [← Nat.add_sub_cancel' hn] at h₁
  obtain ⟨e, he, hcut⟩ := Func.traceOps_cut A hone hW hpos n (U - n) _ _ _ _ _ h₁
    (TraceEnd.notStuck_ok _ _ _)
  rcases hcut with ⟨hj, rfl⟩ | ⟨hk, t₀, s₀, rfl, hp, ht₀, hb⟩
  · exact .inl ⟨hj, (TraceM.run_inFrame _ _ _).2 ⟨_, he, rfl⟩⟩
  · exact .inr ⟨hk, t₀, _, hp, ht₀, hb, (TraceM.run_inFrame _ _ _).2 ⟨_, he, rfl⟩⟩

end Fir
