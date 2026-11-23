import Fir.Execution.TracePace

/-!
# Cuts of a traced path

What `Fir.Execution.TraceTruncate` proves of a run with more fuel and one
with less: a path of the shorter run is the longer path _cut_
(`TraceEnd.Cut`), the same return with fewer steps left, the same UB, or the
longer path _truncated_ (`TraceEnd.Truncated`), out of fuel after a marked
trace that starts the longer path's. This module gives the two relations and
how they go on after an op, after a call's frame is left, and after the
rule that picks a callee (#235) shows its step.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {A : Type}
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M : Module d} {W : Nat}

/-- A way of ending of the traced layer of marked traces. -/
local notation "End" => TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))

/-- The path `e`, of a run of the ops `os` with `n` steps of fuel, is the
longer path whose marked trace is `t` truncated: it runs out of fuel after a
marked trace that starts `t`, with at most `n` steps, and either shows all
of `t` or has `n ≤ W m + c`, for its `m` steps and a chain of `c` calls
that `os` starts. -/
def TraceEnd.Truncated (M : Module d) (W n : Nat) (os : List (Operation d)) (e : End)
    (t : List (Step A)) : Prop :=
  ∃ t₀ s₀, e = .ok (.ok .fuelExhausted, t₀, s₀) ∧ t₀ <+: t ∧ Step.ticks t₀ ≤ n ∧
    (t₀ = t ∨ ∃ c, M.CallChain os c ∧ n ≤ W * Step.ticks t₀ + c)

/-- The path `e` of a run of the ops `os` with `n` steps of fuel is the path
`e'` of the run with `j` more cut: the same return, leaving `j` fewer steps,
or the same UB, or `e'` truncated. -/
def TraceEnd.Cut (M : Module d) (W j n : Nat) (os : List (Operation d)) (e : End) : End → Prop
  | .ok (.ok (.ret (vs, k)), t, s') =>
    (j ≤ k ∧ e = .ok (.ok (.ret (vs, k - j)), t, s')) ∨ (k < j ∧ e.Truncated M W n os t)
  | .ok (.ok .fuelExhausted, t, _) => e.Truncated M W n os t
  | .error (r, t) => e = .error (r, t) ∨ e.Truncated M W n os t
  | .ok (.error _, _, _) => False

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A truncated path, after the trace `t`, is truncated after `t` too, with a
budget and ops whose chain `c'` bound the fuel that `t` took: at most
`ticks t + m` steps, and `n' ≤ W (ticks t) + W x + c'` whenever the rest's
budget `m` has `m + 1 ≤ W x + W`. -/
theorem TraceEnd.Truncated.after {m n' c' : Nat} {os₁ os : List (Operation d)} {e₁ : End}
    {t t₁ : List (Step A)} (hW : ∀ os c, M.CallChain os c → c + 2 ≤ W)
    (h : e₁.Truncated M W m os₁ t₁) (hticks : Step.ticks t + m ≤ n')
    (hbud : ∀ x, m + 1 ≤ W * x + W → n' ≤ W * Step.ticks t + W * x + c') (hc : M.CallChain os c') :
    (e₁.after t).Truncated M W n' os (t ++ t₁) := by
  obtain ⟨t₀, s₀, rfl, hp, ht₀, hb⟩ := h
  refine ⟨t ++ t₀, s₀, rfl, (List.prefix_append_right_inj t).2 hp, ?_, ?_⟩
  · rw [Step.ticks_append]
    omega
  · rcases hb with rfl | ⟨c₁, hc₁, hm⟩
    · exact .inl rfl
    · have := hW _ _ hc₁
      exact .inr ⟨c', hc, by rw [Step.ticks_append, Nat.mul_add]; exact hbud _ (by omega)⟩

omit [DecidableEq d.Ty] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A path of a callee truncated, its frame left, is a path of the call
truncated, one step of fuel later, for any trace that the callee's starts,
when either the trace is the callee's or its fuel was spent on its steps. -/
theorem TraceEnd.Truncated.call {n : Nat} {os body : List (Operation d)} {e : End}
    {t t' : List (Step A)} (h : e.Truncated M W n body t) (hs : M.callHead? os = some body)
    (ht : t <+: t')
    (hb : t = t' ∨ ∃ c, M.CallChain body c ∧ n + 1 ≤ W * Step.ticks t + c + 1) :
    TraceEnd.Truncated M W (n + 1) os
      (e.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit })) t' := by
  obtain ⟨t₀, s₀, rfl, hp, ht₀, hb₀⟩ := h
  refine ⟨t₀, _, rfl, hp.trans ht, by omega, ?_⟩
  rcases hb₀ with rfl | ⟨c, hc, hn⟩
  · rcases hb with rfl | ⟨c, hc, hn⟩
    · exact .inl rfl
    · exact .inr ⟨c + 1, .call hs hc, by omega⟩
  · exact .inr ⟨c + 1, .call hs hc, by omega⟩

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A cut of a path that goes on after an op of one step, from ops that start
no call, is a cut one step of fuel later. -/
theorem TraceEnd.Cut.after_step {j m : Nat} {os₁ os : List (Operation d)}
    (hW : ∀ os c, M.CallChain os c → c + 2 ≤ W) (hos : M.callHead? os = none)
    {t : List (Step A)} (ht : Step.ticks t = 1) {e₁ : End} :
    ∀ {e₁' : End}, e₁.Cut M W j m os₁ e₁' → (e₁.after t).Cut M W j (m + 1) os (e₁'.after t)
  | .ok (.ok (.ret _), _, _), .inl ⟨hj, he⟩ => .inl ⟨hj, by rw [he]; rfl⟩
  | .ok (.ok (.ret _), _, _), .inr ⟨hk, h⟩ =>
    .inr ⟨hk, h.after hW (by omega) (fun _ _ => by rw [ht]; omega) (.stop hos)⟩
  | .ok (.ok .fuelExhausted, _, _), h =>
    h.after hW (by omega) (fun _ _ => by rw [ht]; omega) (.stop hos)
  | .error _, .inl he => .inl (by rw [he]; rfl)
  | .error _, .inr h => .inr (h.after hW (by omega) (fun _ _ => by rw [ht]; omega) (.stop hos))
  | .ok (.error _, _, _), h => h.elim

omit [DecidableEq d.Ty] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A path of a callee truncated, its frame left, after the step of the rule
that picked the callee, is a path of the call truncated, two steps of fuel
later, the rule's and the call's, for any trace that the callee's starts,
when either the trace is the callee's or its fuel was spent on its steps. -/
theorem TraceEnd.Truncated.picked {m : Nat} {os body : List (Operation d)} {e : End}
    {t t' t₀ : List (Step A)} (hW : ∀ os c, M.CallChain os c → c + 2 ≤ W)
    (h : e.Truncated M W m body t) (hos : M.callHead? os = none) (ht₀ : Step.ticks t₀ = 1)
    (ht : t <+: t') (hb : t = t' ∨ ∃ c, M.CallChain body c ∧ m ≤ W * Step.ticks t + c) :
    TraceEnd.Truncated M W (m + 2) os
      (TraceEnd.after t₀ (e.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit })))
      (t₀ ++ t') := by
  obtain ⟨t₁, s₀, rfl, hp, ht₁, hb₁⟩ := h
  have bound : ∀ {c t₂}, M.CallChain body c → m ≤ W * Step.ticks t₂ + c →
      m + 2 ≤ W * Step.ticks (t₀ ++ t₂) + 0 := fun hc hm => by
    have := hW _ _ hc
    rw [Step.ticks_append, ht₀, Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨t₀ ++ t₁, _, rfl, (List.prefix_append_right_inj t₀).2 (hp.trans ht), ?_, ?_⟩
  · rw [Step.ticks_append, ht₀]
    omega
  rcases hb₁ with rfl | ⟨c, hc, hn⟩
  · rcases hb with rfl | ⟨c, hc, hn⟩
    · exact .inl rfl
    · exact .inr ⟨0, .stop hos, bound hc hn⟩
  · exact .inr ⟨0, .stop hos, bound hc hn⟩

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A path of a run with one step of fuel that runs out of fuel after the step
`t₀` of the rule that picks a callee cuts each path that goes on after `t₀`
and, when it returns, has shown a step after `t₀` and is paced. -/
theorem TraceEnd.Cut.pickExh {j : Nat} {os : List (Operation d)} {t₀ : List (Step A)}
    {s₁ : TraceState Mem unit} (hpos : 0 < W) (hos : M.callHead? os = none)
    (ht₀ : Step.ticks t₀ = 1) {e₁ : End} (hne : TraceEnd.NotStuck e₁)
    (hp : TraceEnd.RetPaced M W (j + 1) os (e₁.after t₀))
    (hpos₁ : ∀ vs k t s', e₁ = .ok (.ok (.ret (vs, k)), t, s') → 0 < Step.ticks t) :
    TraceEnd.Cut M W j 1 os (.ok (.ok .fuelExhausted, t₀, s₁)) (e₁.after t₀) := by
  have htr : ∀ t, TraceEnd.Truncated M W 1 os (.ok (.ok .fuelExhausted, t₀, s₁)) (t₀ ++ t) :=
    fun t => ⟨t₀, s₁, rfl, List.prefix_append _ _, by omega,
      .inr ⟨0, .stop hos, by rw [ht₀, Nat.mul_one]; omega⟩⟩
  rcases e₁ with ⟨r, t⟩ | ⟨y, t, s'⟩
  · exact .inr (htr t)
  · rcases y with st | (⟨vs, k⟩ | _)
    · exact absurd rfl (hne st t s')
    · have h₁ := hpos₁ vs k t s' rfl
      obtain ⟨hk, -⟩ := hp
      simp only [Step.ticks_append, ht₀] at hk
      exact .inr ⟨by omega, htr t⟩
    · exact htr t

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
    [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] in
/-- A cut is not stuck. -/
theorem TraceEnd.Cut.notStuck {j n : Nat} {os : List (Operation d)} {e : End} :
    ∀ {e' : End}, e.Cut M W j n os e' → TraceEnd.NotStuck e
  | .ok (.ok (.ret _), _, _), .inl ⟨_, he⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .ok (.ok (.ret _), _, _), .inr ⟨_, _, _, he, _⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .ok (.ok .fuelExhausted, _, _), ⟨_, _, he, _⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .error _, .inl he => he ▸ TraceEnd.notStuck_error _ _
  | .error _, .inr ⟨_, _, he, _⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .ok (.error _, _, _), h => h.elim

end Fir
