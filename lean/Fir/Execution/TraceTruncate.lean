import Fir.Execution.TracePace

/-!
# Truncating a traced run

A traced run with more fuel takes the same paths as one with less, further.
In the traced layer of marked traces, let every path of every op show
exactly one step, and let `W` exceed the length of every chain of calls of
the module by at least one. Then each path of a run of ops with `j` more
steps of fuel is _cut_ to a path of the run with fewer, from the same
environment and traced state:

* a return that leaves at least `j` steps is a return of the smaller run,
  with the same values, acts and traced state, that leaves `j` fewer; UB is
  UB of the smaller run, after the same acts;
* otherwise the smaller run runs out of fuel, _truncated_: after a marked
  trace that starts the longer path's, with at most as many steps as its
  budget _n_. If it shows less than the longer path, it has taken enough
  steps for its budget: `n ≤ W m + c`, where `m` is its number of steps and
  `c` the length of the chain of calls that its ops start. That is, it spent
  at most `W` steps of fuel on each step, and at most `c` on the calls
  before its first, and the longer path's next step comes before `W` more
  steps of fuel.

The proof follows the ways a step goes on, by strong induction on the
smaller budget. An op that runs by its own rule takes one step of fuel in
both runs and shows one step. A call spends one step of fuel and goes on in
its callee, one call further along the chain of its ops. When the callee
returns in both runs, the caller goes on in both with the steps they leave,
`j` apart; the fuel the callee spent is paced by its steps
(`Fir.Execution.TracePace`). When the callee returns only in the longer run,
the cut is in the callee: its truncated path shows all of the callee's acts
at most when the callee spent its fuel on its steps.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {A : Type}
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] {M : Module d} {W : Nat}

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

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] in
/-- A truncated path, after the trace `t`, is truncated after `t` too, with a
budget and ops whose chain `c'` bound the fuel that `t` took: at most
`ticks t + m` steps, and `n' ≤ W (ticks t) + W x + c'` whenever the rest's
budget `m` has `m + 1 ≤ W x + W`. -/
theorem TraceEnd.Truncated.after {m n' c' : Nat} {os₁ os : List (Operation d)} {e₁ : End}
    {t t₁ : List (Step A)} (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W)
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

omit [DecidableEq d.Ty] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] in
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

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] in
/-- A cut of a path that goes on after an op of one step, from ops that start
no call, is a cut one step of fuel later. -/
theorem TraceEnd.Cut.after_step {j m : Nat} {os₁ os : List (Operation d)}
    (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W) (hos : M.callHead? os = none)
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

omit [DecidableEq d.Ty] [DecidableEq Mem] [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] in
/-- A cut is not stuck. -/
theorem TraceEnd.Cut.notStuck {j n : Nat} {os : List (Operation d)} {e : End} :
    ∀ {e' : End}, e.Cut M W j n os e' → TraceEnd.NotStuck e
  | .ok (.ok (.ret _), _, _), .inl ⟨_, he⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .ok (.ok (.ret _), _, _), .inr ⟨_, _, _, he, _⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .ok (.ok .fuelExhausted, _, _), ⟨_, _, he, _⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .error _, .inl he => he ▸ TraceEnd.notStuck_error _ _
  | .error _, .inr ⟨_, _, he, _⟩ => he ▸ TraceEnd.notStuck_ok _ _ _
  | .ok (.error _, _, _), h => h.elim

/-- A way of ending that is not stuck is not stuck after a trace. -/
theorem TraceEnd.NotStuck.after {B σ ε α : Type} {t : List B} {e : TraceEnd B σ (Except ε α)}
    (h : TraceEnd.NotStuck e) : TraceEnd.NotStuck (e.after t) := by
  rcases e with ⟨_, _⟩ | ⟨y, t', s⟩
  · exact TraceEnd.notStuck_error _ _
  · rcases y with er | a
    · exact absurd rfl (h er t' s)
    · exact TraceEnd.notStuck_ok _ _ _

variable (A) in
/-- Each path of a traced run of ops with `j` more steps of fuel that is not
stuck is cut to a path of the run with `n`, from the same environment and
traced state, when every path of every op shows exactly one step and `W`
exceeds the length of every chain of calls of the module by at least one. -/
theorem Func.traceOps_cut (hone : OpsOneStep d A (TraceState Mem unit))
    (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W) (hpos : 0 < W) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)) (s : TraceState Mem unit)
      (e' : End), Func.traceOps (Step A) M (n + j) f env os s e' → TraceEnd.NotStuck e' →
      ∃ e, Func.traceOps (Step A) M n f env os s e ∧ e.Cut M W j n os e' := by
  have hpace := Func.traceOps_retPaced A hone hW
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os s e' he' hne
    match n, os, he' with
    | 0, os, he' =>
      refine ⟨_, Func.traceOps_zero.2 rfl, ?_⟩
      have htr : ∀ t : List (Step A), (t = [] ∨ ∃ c, M.CallChain os c) →
          TraceEnd.Truncated M W 0 os (.ok (.ok .fuelExhausted, [], s)) t := fun t ht =>
        ⟨[], s, rfl, List.nil_prefix, Nat.le_refl _,
          ht.imp (fun h => h.symm) fun ⟨c, hc⟩ => ⟨c, hc, Nat.zero_le _⟩⟩
      by_cases hch : ∃ c, M.CallChain os c
      · rcases e' with ⟨r, t⟩ | ⟨y, t, s'⟩
        · exact .inr (htr t (.inr hch))
        · rcases y with st | (⟨vs, k⟩ | _)
          · exact absurd rfl (hne st t s')
          · obtain ⟨hk, hp, -⟩ := hpace _ f env os s _ he' hne
            exact .inr ⟨by omega, htr t (.inr hch)⟩
          · exact htr t (.inr hch)
      · obtain ⟨s', rfl⟩ := Func.traceOps_silent _ f env os s (fun c hc => hch ⟨c, hc⟩) e' he' hne
        exact htr [] (.inl rfl)
    | n + 1, [], he' =>
      rw [Nat.add_right_comm] at he'
      exact absurd he' (Func.traceOps_nil hne)
    | n + 1, o :: os, he' =>
      rw [Nat.add_right_comm] at he'
      have ihn := ih n (Nat.lt_succ_self n)
      have mk : ∀ {x}, TraceEnd.NotStuck x → Func.TStepPath M n f env o os s x →
          Func.traceOps (Step A) M (n + 1) f env (o :: os) s x :=
        fun hx h => (Func.tStepPath_iff hx).2 h
      cases (Func.tStepPath_iff hne).1 he' with
      | exitUB hreg hargs hT hos hx =>
        exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.exitUB hreg hargs hT hos hx), .inl rfl⟩
      | ret hreg hargs hT hos hx hs =>
        refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.ret hreg hargs hT hos hx hs),
          .inl ⟨Nat.le_add_left _ _, ?_⟩⟩
        rw [Nat.add_sub_cancel]
      | goto hreg hargs hT hos hx hj h =>
        obtain ⟨e₁, h₁, hcut⟩ := ihn j _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)
        exact ⟨_, mk hcut.notStuck.after (.goto hreg hargs hT hos hx hj h₁),
          hcut.after_step hW (Module.callHead?_terminator os hT) ((hone _ _ _).2 _ hx)⟩
      | denoteUB hreg hargs hT hc hx =>
        exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.denoteUB hreg hargs hT hc hx), .inl rfl⟩
      | denote hreg hargs hT hc hx hlen h =>
        obtain ⟨e₁, h₁, hcut⟩ := ihn j _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)
        exact ⟨_, mk hcut.notStuck.after (.denote hreg hargs hT hc hx hlen h₁),
          hcut.after_step hW (Module.callHead?_noCallee os hc) ((hone _ _ _).1 _ hx)⟩
      | callUB hreg hargs hT hc hg hen hx =>
        obtain ⟨e₁', h₁', he₁'⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁' with ⟨r₁, t₁⟩ | ⟨_, _, _⟩
        · simp only [Except.map, Except.error.injEq] at he₁'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj he₁'
          obtain ⟨e₁, h₁, hcut⟩ := ihn j _ _ _ _ _ h₁' (TraceEnd.notStuck_error _ _)
          rcases hcut with rfl | htr
          · exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.callUB hreg hargs hT hc hg hen
              ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), .inl rfl⟩
          · have htr' := htr.call (Module.callHead?_call os hT hc hg hen) (List.prefix_refl _)
              (.inl rfl)
            obtain ⟨t₀, s₀, rfl, -⟩ := htr
            exact ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT hc hg hen
              ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), .inr htr'⟩
        · cases he₁'
      | callExh hreg hargs hT hc hg hen hx =>
        obtain ⟨e₁', h₁', he₁'⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁' with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
        · cases he₁'
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁'
        obtain ⟨rfl, rfl, -⟩ := he₁'
        obtain ⟨e₁, h₁, htr⟩ := ihn j _ _ _ _ _ h₁' (TraceEnd.notStuck_ok _ _ _)
        have htr' := TraceEnd.Truncated.call htr (Module.callHead?_call os hT hc hg hen)
          (List.prefix_refl _) (.inl rfl)
        obtain ⟨t₀, s₀, rfl, -⟩ := htr
        exact ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT hc hg hen
          ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), htr'⟩
      | @callRet args sym g body genv vs k₁ tc s₁ e₂' hreg hargs hT hc hg hen hx hty hlen h =>
        obtain ⟨e₁', h₁', he₁'⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁' with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
        · cases he₁'
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁'
        obtain ⟨rfl, rfl, rfl⟩ := he₁'
        obtain ⟨hk₁, hp₁, c₁, hc₁, hb₁⟩ := hpace _ _ _ _ _ _ h₁' (TraceEnd.notStuck_ok _ _ _)
        rw [Nat.min_eq_left (by omega : k₁ ≤ n + j)] at h
        have hs := Module.callHead?_call os hT hc hg hen
        have hW₁ := hW _ _ hc₁
        obtain ⟨e₁, h₁, hcut₁⟩ := ihn j _ _ _ _ _ h₁' (TraceEnd.notStuck_ok _ _ _)
        rcases hcut₁ with ⟨hj, rfl⟩ | ⟨hk, htr⟩
        · -- The callee returns in both runs; the caller goes on with steps `j` apart.
          obtain ⟨hk₁', -, c₁', hc₁', hb₁'⟩ := hpace _ _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
          have hW₁' := hW _ _ hc₁'
          replace hk₁' : k₁ - j + Step.ticks tc ≤ n := hk₁'
          rw [← Nat.sub_add_cancel hj] at h
          obtain ⟨e₂, h₂, hcut₂⟩ := ih (k₁ - j) (by omega) j _ _ _ _ _ h
            (TraceEnd.NotStuck.of_after hne)
          refine ⟨_, mk hcut₂.notStuck.after (.callRet hreg hargs hT hc hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩) hty hlen
            ((Nat.min_eq_left (by omega : k₁ - j ≤ n)).symm ▸ h₂)), ?_⟩
          have hbud : ∀ x, k₁ - j + 1 ≤ W * x + W →
              n + 1 ≤ W * Step.ticks tc + W * x + (c₁' + 1) := fun x hx => by omega
          have hcall := Module.CallChain.call hs hc₁'
          have hticks : Step.ticks tc + (k₁ - j) ≤ n + 1 := by omega
          rcases e₂' with ⟨r, t₂⟩ | ⟨y₂, t₂, s₃⟩
          · rcases hcut₂ with rfl | htr
            · exact .inl rfl
            · exact .inr (htr.after hW hticks hbud hcall)
          · rcases y₂ with st | (⟨vs₂, k₂⟩ | _)
            · exact hcut₂.elim
            · rcases hcut₂ with ⟨hj₂, rfl⟩ | ⟨hk₂, htr⟩
              · exact .inl ⟨hj₂, rfl⟩
              · exact .inr ⟨hk₂, htr.after hW hticks hbud hcall⟩
            · exact TraceEnd.Truncated.after hW hcut₂ hticks hbud hcall
        · -- The callee is cut: it ran out of fuel, its fuel spent on its steps.
          have htr' : ∀ t₂, TraceEnd.Truncated M W (n + 1) (o :: os)
              (e₁.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit })) (tc ++ t₂) :=
            fun t₂ => htr.call hs (List.prefix_append _ _) (.inr ⟨c₁, hc₁, by omega⟩)
          obtain ⟨t₀, s₀, rfl, -⟩ := htr
          refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT hc hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), ?_⟩
          rcases e₂' with ⟨r, t₂⟩ | ⟨y₂, t₂, s₃⟩
          · exact .inr (htr' t₂)
          · rcases y₂ with st | (⟨vs₂, k₂⟩ | _)
            · exact absurd rfl (TraceEnd.NotStuck.of_after hne st t₂ s₃)
            · obtain ⟨hk₂, -⟩ := hpace _ _ _ _ _ _ h (TraceEnd.notStuck_ok _ _ _)
              exact .inr ⟨by omega, htr' t₂⟩
            · exact htr' t₂

end Fir
