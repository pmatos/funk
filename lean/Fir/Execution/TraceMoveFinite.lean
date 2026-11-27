import Fir.Execution.TraceMoveCases
import Fir.Execution.TraceBlackBox

/-!
# Finitely many moves

When every op that runs by its own rule, every external call and every rule
that picks a callee has finitely many outcomes, given the world's answers, a
configuration has finitely many moves of at most two steps of fuel whose
acts agree with an answer stream (`TCfg.moves_finite`): the outcomes of its
first op or of its external call, the callee it may enter, and the returns
of a callee with one step of fuel; and finitely many calls of a function
of the module (`TCfg.calls_finite`). A call whose callee is picked (#235)
calls one of finitely many symbols, after one of finitely many outcomes of
its rule (`Func.TCallsAt.finite`).
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {M : Module d}

omit [DecidableEq Mem] in
/-- A list with an element related to infinitely many numbers has one element
related to infinitely many. -/
theorem List.exists_often_of_mem {α : Type} {Q : Nat → α → Prop} :
    ∀ {L : List α}, (∀ m, ∃ n, m ≤ n ∧ ∃ a ∈ L, Q n a) → ∃ a ∈ L, ∀ m, ∃ n, m ≤ n ∧ Q n a
  | [], h => by
    obtain ⟨_, _, _, ha, _⟩ := h 0
    cases ha
  | a :: L, h => by
    by_cases ha : ∀ m, ∃ n, m ≤ n ∧ Q n a
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨m₀, hm₀⟩ := Classical.not_forall.1 ha
      obtain ⟨b, hb, hq⟩ := List.exists_often_of_mem (L := L) fun m => by
        obtain ⟨n, hn, x, hx, hQ⟩ := h (max m m₀)
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd ⟨n, Nat.le_trans (Nat.le_max_right _ _) hn, hQ⟩ hm₀
        · exact ⟨n, Nat.le_trans (Nat.le_max_left _ _) hn, x, hx, hQ⟩
      exact ⟨b, List.mem_cons_of_mem _ hb, hq⟩

/-! # Finitely many moves of one step -/

variable {E Ans : Type} [DialectDenote d (TraceM (Step (Act E Ans)) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step (Act E Ans)) (TraceState Mem unit))]

omit [DecidableEq Mem] in
/-- An op calls, on its operands and from a traced state, finitely many
symbols on finitely many arguments, after finitely many steps and acts that
agree with an answer stream, from finitely many traced states: one callee
when it names it, and one for each outcome of the rule that picks it
otherwise, which has finitely many. -/
theorem Func.TCallsAt.finite (hfin : OpsStepFinite d E Ans (TraceState Mem unit))
    (o : Operation d) (args : HVector toType (sig o.op)) (s : TraceState Mem unit)
    (ans : Nat → Option Ans) :
    ∃ L : List (Nat × List (Step (Act E Ans)) × TraceState Mem unit × Name × List (DVal d)),
      ∀ δ sym ts (cargs : HVector toType ts) t₀ s₁,
        Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ → Act.Agrees ans (Step.actsOf t₀) →
        (δ, t₀, s₁, sym, cargs.toDVals) ∈ L := by
  cases hc : callee? o.op with
  | none => exact ⟨[], fun _ _ _ _ _ _ h => by cases h <;> simp_all⟩
  | some c =>
  cases c with
  | fixed sym =>
    refine ⟨[(0, [], s, sym, args.toDVals)], fun δ sym' ts cargs t₀ s₁ h _ => ?_⟩
    cases h with
    | fixed hc' => rw [hc'] at hc; cases hc; exact List.mem_singleton_self _
    | picked hc' => rw [hc'] at hc; cases hc
  | picked =>
    obtain ⟨L, hL⟩ := hfin.2.2 o.op hc (M.callable (sig o.op).tail (returnTypes o.op)) args s ans
    refine ⟨L.map fun p => (1, p.2.1, p.2.2, p.1, args.tail.toDVals),
      fun δ sym ts cargs t₀ s₁ h hag => ?_⟩
    cases h with
    | fixed hc' => rw [hc'] at hc; cases hc
    | picked _ hs => exact List.mem_map.2 ⟨_, hL _ _ _ hs hag, rfl⟩

omit [DecidableEq Mem] in
/-- Acts that agree with a stream, the first of them a call's, are the call's
acts agreeing with it, then the rest agreeing with it after them. -/
theorem Act.agrees_actsOf_append {ans : Nat → Option Ans} {t₀ t : List (Step (Act E Ans))}
    (h : Act.Agrees ans (Step.actsOf (t₀ ++ t))) :
    Act.Agrees ans (Step.actsOf t₀) ∧
      Act.Agrees (fun i => ans ((Step.actsOf t₀).length + i)) (Step.actsOf t) := by
  rw [Step.actsOf_append] at h
  exact Act.agrees_append.1 h

/-- When every op that runs by its own rule, every external call and every
rule that picks a callee has finitely many outcomes, given the world's
answers, a configuration has finitely many moves of at most two steps of
fuel whose acts agree with an answer stream: the outcomes of its first op,
each with the configuration it goes on to; the outcomes of its external
call; the callee it may enter; and the returns of a callee with one step of
fuel. -/
theorem TCfg.moves_finite (hfin : OpsStepFinite d E Ans (TraceState Mem unit))
    (c : TCfg d Mem unit) (ans : Nat → Option Ans) :
    ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))), ∀ c₁ t F,
      TCfg.Move (Act E Ans) M c c₁ t F → F ≤ 2 → Act.Agrees ans (Step.actsOf t) → (c₁, t) ∈ L := by
  rcases c with ⟨f, env, os, s⟩
  cases os with
  | nil => exact ⟨[], fun c₁ t F h => by cases h⟩
  | cons o os =>
    cases hargs : env.operands (sig o.op) o.operands with
    | error _ =>
      refine ⟨[], fun c₁ t F h _ _ => ?_⟩
      cases h <;> simp_all
    | ok args =>
      have Ld : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          isTerminator o.op = false → callee? o.op = none →
          ∀ (rs : HVector toType (returnTypes o.op)) t s₁,
            DialectDenote.denote (m := TraceM (Step (Act E Ans)) (TraceState Mem unit)) o.op args s
              (.ok (rs, t, s₁)) → Act.Agrees ans (Step.actsOf t) →
            (⟨f, (o.results.map (·.1)).zip rs.toDVals ++ env, os, s₁⟩, t) ∈ L := by
        by_cases hk : isTerminator o.op = false ∧ callee? o.op = none
        · obtain ⟨L₀, hL₀⟩ := ((hfin.1 o.op (.inr hk.2) args).1 hk.1) s ans
          exact ⟨L₀.map fun p => (⟨f, (o.results.map (·.1)).zip p.1.toDVals ++ env, os, p.2.2⟩, p.2.1),
            fun _ _ rs t s₁ hx hag => List.mem_map.2 ⟨_, hL₀ _ _ _ hx hag, rfl⟩⟩
        · exact ⟨[], fun hT hc => absurd ⟨hT, hc⟩ hk⟩
      have Le : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          isTerminator o.op = true → ∀ i t s₁ (b : Block d) env₁,
            DialectDenote.exit (m := TraceM (Step (Act E Ans)) (TraceState Mem unit)) o.op args s
              (.ok (.goto i, t, s₁)) → f.jump env o.succs i = .ok (b, env₁) →
            Act.Agrees ans (Step.actsOf t) → (⟨f, env₁, b.body, s₁⟩, t) ∈ L := by
        by_cases hT : isTerminator o.op = true
        · obtain ⟨L₀, hL₀⟩ := ((hfin.1 o.op (.inl hT) args).2 hT) s ans
          refine ⟨L₀.filterMap fun p => match p.1 with
            | .goto i => match f.jump env o.succs i with
              | .ok (b, env₁) => some (⟨f, env₁, b.body, p.2.2⟩, p.2.1)
              | .error _ => none
            | .ret => none, fun _ i t s₁ b env₁ hx hj hag => ?_⟩
          exact List.mem_filterMap.2 ⟨_, hL₀ _ _ _ hx hag, by simp [hj]⟩
        · exact ⟨[], fun h => absurd h hT⟩
      obtain ⟨Lk, hLk⟩ := Func.TCallsAt.finite (M := M) hfin o args s ans
      have Lx : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          ∀ δ sym ts (cargs : HVector toType ts) t₀ s₁ (vs : List (DVal d)) t s₂,
            Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ →
            DialectExtCall.extCall (m := TraceM (Step (Act E Ans)) (TraceState Mem unit)) sym
              cargs.toDVals (returnTypes o.op) s₁ (.ok (vs, t, s₂)) →
            Act.Agrees ans (Step.actsOf (t₀ ++ t)) →
            (⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩, t₀ ++ t) ∈ L := by
        obtain ⟨C, hC⟩ := List.exists_cover (L := Lk) (P := fun κ p => ∃ vs t s₂,
            DialectExtCall.extCall (m := TraceM (Step (Act E Ans)) (TraceState Mem unit))
              κ.2.2.2.1 κ.2.2.2.2 (returnTypes o.op) κ.2.2.1 (.ok (vs, t, s₂)) ∧
            Act.Agrees (fun i => ans ((Step.actsOf κ.2.1).length + i)) (Step.actsOf t) ∧
            p = ((⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ : TCfg d Mem unit), κ.2.1 ++ t))
          fun κ _ => by
            obtain ⟨L₁, hL₁⟩ := (hfin.2.1 κ.2.2.2.1 κ.2.2.2.2 (returnTypes o.op)) κ.2.2.1
              (fun i => ans ((Step.actsOf κ.2.1).length + i))
            exact ⟨L₁.map fun q => (⟨f, (o.results.map (·.1)).zip q.1 ++ env, os, q.2.2⟩,
              κ.2.1 ++ q.2.1), fun p ⟨vs, t, s₂, hx, hag, hp⟩ =>
                hp ▸ List.mem_map.2 ⟨_, hL₁ _ _ _ hx hag, rfl⟩⟩
        refine ⟨C, fun δ sym ts cargs t₀ s₁ vs t s₂ hc hx hag => ?_⟩
        obtain ⟨h₀, h₁⟩ := Act.agrees_actsOf_append hag
        exact hC _ (hLk _ _ _ _ _ _ hc h₀) _ ⟨vs, t, s₂, hx, h₁, rfl⟩
      have Lc : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          ∀ δ sym ts (cargs : HVector toType ts) t₀ s₁ (g : Func d) body genv,
            Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ → M.func? sym = some g →
            g.enter cargs.toDVals = .ok (body, genv) → Act.Agrees ans (Step.actsOf t₀) →
            ((⟨g, genv, body, { s₁ with mem := s₁.mem.enter }⟩ : TCfg d Mem unit), t₀) ∈ L := by
        refine ⟨Lk.filterMap fun κ => match M.func? κ.2.2.2.1 with
          | some g => match g.enter κ.2.2.2.2 with
            | .ok (body, genv) => some (⟨g, genv, body, { κ.2.2.1 with mem := κ.2.2.1.mem.enter }⟩,
                κ.2.1)
            | .error _ => none
          | none => none, fun δ sym ts cargs t₀ s₁ g body genv hc hg hen hag => ?_⟩
        exact List.mem_filterMap.2 ⟨_, hLk _ _ _ _ _ _ hc hag, by simp [hg, hen]⟩
      have Lr : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          ∀ δ sym ts (cargs : HVector toType ts) t₀ s₁ (g : Func d) body genv
            (vs : List (DVal d)) k t s₂,
            Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ → M.func? sym = some g →
            g.enter cargs.toDVals = .ok (body, genv) →
            Func.traceCall (Step (Act E Ans)) M 1 g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s₂)) →
            Act.Agrees ans (Step.actsOf (t₀ ++ t)) →
            (⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩, t₀ ++ t) ∈ L := by
        obtain ⟨C, hC⟩ := List.exists_cover (L := Lk) (P := fun κ p =>
            ∃ (g : Func d) (body : List (Operation d)) (genv : Env d) (vs : List (DVal d)) (k : Nat)
              (t : List (Step (Act E Ans))) (s₂ : TraceState Mem unit),
            M.func? κ.2.2.2.1 = some g ∧ g.enter κ.2.2.2.2 = .ok (body, genv) ∧
            Func.traceCall (Step (Act E Ans)) M 1 g genv body κ.2.2.1
              (.ok (.ok (.ret (vs, k)), t, s₂)) ∧
            Act.Agrees (fun i => ans ((Step.actsOf κ.2.1).length + i)) (Step.actsOf t) ∧
            p = ((⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ : TCfg d Mem unit), κ.2.1 ++ t))
          fun κ _ => by
            cases hg : M.func? κ.2.2.2.1 with
            | none => exact ⟨[], fun _ ⟨_, _, _, _, _, _, _, h, _⟩ => by simp_all⟩
            | some g =>
            cases hen : g.enter κ.2.2.2.2 with
            | error _ => exact ⟨[], fun _ ⟨_, _, _, _, _, _, _, h, h', _⟩ => by simp_all⟩
            | ok p =>
            obtain ⟨L₁, hL₁⟩ := (ExceptStepFinite.inFrame (Func.traceOps_finite hfin M 1 g p.2 p.1))
              κ.2.2.1 (fun i => ans ((Step.actsOf κ.2.1).length + i))
            refine ⟨L₁.filterMap fun q => match q.1 with
              | .ret (vs, _) => some (⟨f, (o.results.map (·.1)).zip vs ++ env, os, q.2.2⟩, κ.2.1 ++ q.2.1)
              | .fuelExhausted => none, fun p' ⟨g', body, genv, vs, k, t, s₂, hg', hen', hx, hag, hp⟩ => ?_⟩
            cases hg'
            rw [hen] at hen'
            cases hen'
            exact hp ▸ List.mem_filterMap.2 ⟨_, hL₁ _ _ _ hx hag, rfl⟩
        refine ⟨C, fun δ sym ts cargs t₀ s₁ g body genv vs k t s₂ hc hg hen hx hag => ?_⟩
        obtain ⟨h₀, h₁⟩ := Act.agrees_actsOf_append hag
        exact hC _ (hLk _ _ _ _ _ _ hc h₀) _ ⟨g, body, genv, vs, k, t, s₂, hg, hen, hx, h₁, rfl⟩
      obtain ⟨Ld, hLd⟩ := Ld
      obtain ⟨Le, hLe⟩ := Le
      obtain ⟨Lx, hLx⟩ := Lx
      obtain ⟨Lc, hLc⟩ := Lc
      obtain ⟨Lr, hLr⟩ := Lr
      refine ⟨Lx ++ (Ld ++ Le ++ Lc ++ Lr), fun c₁ t F h hF hag => ?_⟩
      cases h with
      | denote _ hargs' hT hc hx =>
        rw [hargs] at hargs'
        cases hargs'
        simp only [List.mem_append]
        exact .inr (.inl (.inl (.inl (hLd hT hc _ _ _ hx hag))))
      | ext _ hargs' _ hc _ _ hx =>
        rw [hargs] at hargs'
        cases hargs'
        exact List.mem_append_left _ (hLx _ _ _ _ _ _ _ _ _ hc hx hag)
      | goto _ hargs' hT _ hx hj =>
        rw [hargs] at hargs'
        cases hargs'
        simp only [List.mem_append]
        exact .inr (.inl (.inl (.inr (hLe hT _ _ _ _ _ hx hj hag))))
      | enter _ hargs' _ hc hg hen =>
        rw [hargs] at hargs'
        cases hargs'
        simp only [List.mem_append]
        exact .inr (.inl (.inr (hLc _ _ _ _ _ _ _ _ _ hc hg hen hag)))
      | @ret _ _ _ _ _ _ _ _ δ _ _ _ _ _ _ _ U _ _ _ _ hargs' _ hc hg hen hx =>
        rw [hargs] at hargs'
        cases hargs'
        cases U with
        | zero =>
          obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 hx
          cases Func.traceOps_zero.1 h₁
          cases he₁
        | succ U =>
          obtain rfl : U = 0 := by omega
          simp only [List.mem_append]
          exact .inr (.inr (hLr _ _ _ _ _ _ _ _ _ _ _ _ _ hc hg hen hx hag))

omit [DecidableEq Mem] in
/-- When every rule that picks a callee has finitely many outcomes, given
the world's answers, a configuration's first op calls finitely many
functions of the module, after finitely many steps and acts that agree with
an answer stream, from finitely many traced states. -/
theorem TCfg.calls_finite (hfin : OpsStepFinite d E Ans (TraceState Mem unit))
    (c : TCfg d Mem unit) (ans : Nat → Option Ans) :
    ∃ L : List (Nat × List (Step (Act E Ans)) × TraceState Mem unit × Func d ×
        List (Operation d) × Env d),
      ∀ δ t₀ s₁ g body genv, c.Calls M δ t₀ s₁ g body genv → Act.Agrees ans (Step.actsOf t₀) →
        (δ, t₀, s₁, g, body, genv) ∈ L := by
  classical
  rcases c with ⟨f, env, os, s⟩
  cases os with
  | nil => exact ⟨[], fun _ _ _ _ _ _ ⟨_, _, h, _⟩ => by cases h⟩
  | cons o os =>
    cases hargs : env.operands (sig o.op) o.operands with
    | error _ =>
      refine ⟨[], fun _ _ _ _ _ _ ⟨o', os', hos, _, _, _, _, _, _, hargs', _⟩ => ?_⟩
      dsimp only at hos hargs'
      cases hos
      simp_all
    | ok args =>
      obtain ⟨Lk, hLk⟩ := Func.TCallsAt.finite (M := M) hfin o args s ans
      refine ⟨Lk.filterMap fun κ => match M.func? κ.2.2.2.1 with
          | some g => match g.enter κ.2.2.2.2 with
            | .ok (body, genv) => some (κ.1, κ.2.1, κ.2.2.1, g, body, genv)
            | .error _ => none
          | none => none,
        fun δ t₀ s₁ g body genv ⟨o', os', hos, _, _, args', sym, ts, cargs, hargs', hc, hg, hen⟩ hag => ?_⟩
      dsimp only at hos hargs' hc
      cases hos
      rw [hargs] at hargs'
      cases hargs'
      exact List.mem_filterMap.2 ⟨_, hLk _ _ _ _ _ _ hc hag, by simp [hg, hen]⟩
end Fir
