import Fir.Execution.TraceGood

/-!
# A move that infinitely many paths take

A configuration whose run shows a stream at unboundedly many budgets
(`TGood`, `Fir.Execution.TraceGood`) has a move after which the next
configuration does too, with the stream after the move's acts and the
deadlines less its steps (`TGood.move`). This is the pigeonhole step of
divergence across a black box, under the hypothesis that the human ruled on
2026-11-20, on #233: every op that runs by its own rule has finitely many
outcomes, given the world's answers.

Take, for each number `m`, a path that sees the stream for `m` acts at a budget
above `m`. Each goes on by a first move (`TCfg.exh_succ`).

* _Infinitely many go on by a move of at most two steps of fuel._ There are
  finitely many such moves whose acts agree with the stream's answers
  (`TCfg.moves_finite`), so one is taken by infinitely many.
* _Otherwise, from some `m` on, the first op calls a function and its callee
  returns._ The op calls one of finitely many functions, after the steps and
  acts of the rule that picks it, if any (#235), from one of finitely many
  traced states (`TCfg.calls_finite`), so one call is taken by infinitely
  many paths.
  * When the callee's returns show unboundedly many steps, the configuration
    enters the callee: cut at a budget `b`, large but below the steps of a
    return, the callee runs out of fuel after the return's first steps, which
    show the stream's first acts within their deadlines.
  * When they show at most `J` steps, the callee's fuel is at most `W J`
    (`Func.traceCall_retPaced_le`), so each return is a return at that one
    budget, of which there are finitely many (`Func.traceOps_finite`). One is
    taken by infinitely many paths, and the rest runs out of fuel at budgets
    at least theirs less `W J`.
-/

namespace Fir

open Memory

variable {E Ans : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step (Act E Ans)) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step (Act E Ans)) (TraceState Mem unit))] {M : Module d}

/-- A configuration whose run shows a stream at unboundedly many budgets, for
each number of acts, goes on by a move to a configuration whose run shows the
stream after the move's acts, with deadlines less its steps. The move shows the
stream's first acts, and each deadline after them is at least its steps. It
asks that every path of every op show exactly one step, and that every op that
runs by its own rule have finitely many outcomes, given the world's
answers. -/
theorem TGood.move (hone : OpsOneStep d (Act E Ans) (TraceState Mem unit))
    (hfin : OpsStepFinite d E Ans (TraceState Mem unit)) {c : TCfg d Mem unit}
    {T : Nat → Option (Act E Ans)} {K : Nat → Nat} (h : TGood (c.exh (Act E Ans) M) T K) :
    ∃ c₁ t F, TCfg.Move (Act E Ans) M c c₁ t F ∧
      TGood (c₁.exh (Act E Ans) M) (Stream.drop T (Step.actsOf t).length)
        (Stream.dropK K (Step.actsOf t).length (Step.ticks t)) ∧
      Stream.Cons T (Step.actsOf t) ∧
      ∀ x, Stream.Avail T (x + (Step.actsOf t).length) →
        K (x + (Step.actsOf t).length) < Step.ticks t → x = 0 := by
  let ans : Nat → Option Ans := fun i => (T i).map Act.answer
  -- For each `m`, a path above `m` that sees the stream for `m` acts.
  let Wm : Nat → Nat → List (Step (Act E Ans)) → Prop := fun m n mt =>
    c.exh (Act E Ans) M (n + 1) mt ∧ m ≤ n ∧ TGood.Sees T K m mt
  have hw : ∀ m, ∃ n mt, Wm m n mt := fun m => by
    obtain ⟨n, hn, mt, hx, hs⟩ := h m (m + 1)
    obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨m + n', mt, by rwa [Nat.add_right_comm] at hx, Nat.le_add_right _ _, hs⟩
  have agree : ∀ {m n mt} {t mt₁ : List (Step (Act E Ans))}, Wm m n mt → mt = t ++ mt₁ →
      Act.Agrees ans (Step.actsOf t) := fun hW he =>
    (hW.2.2.1.agrees).of_prefix (Step.actsOf_prefix (he ▸ List.prefix_append _ _))
  let One : Nat → TCfg d Mem unit × List (Step (Act E Ans)) → Prop := fun m p =>
    ∃ n mt mt₁ F, Wm m n mt ∧ TCfg.Move (Act E Ans) M c p.1 p.2 F ∧ F ≤ 2 ∧ F ≤ n + 1 ∧
      p.1.exh (Act E Ans) M (n + 1 - F) mt₁ ∧ mt = p.2 ++ mt₁
  by_cases hI : ∀ m₀, ∃ m, m₀ ≤ m ∧ ∃ p, One m p
  · -- Infinitely many paths go on by a move of at most two steps of fuel.
    obtain ⟨L, hL⟩ := TCfg.moves_finite (M := M) hfin c ans
    obtain ⟨⟨c₁, t⟩, -, hof⟩ := List.exists_often_of_mem (L := L) (Q := One) fun m₀ => by
      obtain ⟨m, hm, p, n, mt, mt₁, F, hW, hmv, hF, hFn, hx, he⟩ := hI m₀
      exact ⟨m, hm, p, hL _ _ _ hmv hF (agree hW he), n, mt, mt₁, F, hW, hmv, hF, hFn, hx, he⟩
    obtain ⟨_, -, _, _, _, F₀, -, hmv, -, -, -, -⟩ := hof 0
    refine ⟨c₁, t, F₀, hmv, TGood.after fun k B => ?_⟩
    obtain ⟨m, hm, n, mt, mt₁, F, hW, -, hF, -, hx, rfl⟩ := hof (k + (Step.actsOf t).length + B + 2)
    exact ⟨n + 1 - F, by have := hW.2.1; omega, mt₁, hx, hW.2.2.mono (by omega)⟩
  -- From some `m₀` on, no path goes on by such a move: each calls a function that returns.
  obtain ⟨m₀, hm₀⟩ := Classical.not_forall.1 hI
  have noOne : ∀ m, m₀ ≤ m → ∀ p, ¬ One m p := fun m hm p hp => hm₀ ⟨m, hm, p, hp⟩
  let Via : Nat → Nat × List (Step (Act E Ans)) × TraceState Mem unit × Func d ×
      List (Operation d) × Env d → Prop := fun m κ =>
    ∃ n mt, Wm m n mt ∧ c.Calls M κ.1 κ.2.1 κ.2.2.1 κ.2.2.2.1 κ.2.2.2.2.1 κ.2.2.2.2.2 ∧
      κ.1 ≤ n ∧ ∃ vs k t s₂ mt₁,
        Func.traceCall (Step (Act E Ans)) M (n - κ.1) κ.2.2.2.1 κ.2.2.2.2.2 κ.2.2.2.2.1 κ.2.2.1
          (.ok (.ok (.ret (vs, k)), t, s₂)) ∧
        (∀ U k', Func.traceCall (Step (Act E Ans)) M U κ.2.2.2.1 κ.2.2.2.2.2 κ.2.2.2.2.1 κ.2.2.1
          (.ok (.ok (.ret (vs, k')), t, s₂)) →
          TCfg.Move (Act E Ans) M c (c.after vs s₂) (κ.2.1 ++ t) (U + κ.1 + 1)) ∧
        (c.after vs s₂).exh (Act E Ans) M (min k (n - κ.1)) mt₁ ∧ mt = κ.2.1 ++ t ++ mt₁
  -- One call, with the steps and acts of its op before it, is taken by infinitely many.
  obtain ⟨Lκ, hLκ⟩ := TCfg.calls_finite (M := M) hfin c ans
  obtain ⟨⟨δ, t₀, s₁, g, body, genv⟩, -, hκ⟩ := List.exists_often_of_mem (L := Lκ) (Q := Via)
    fun m₂ => by
      obtain ⟨n, mt, hW⟩ := hw (max m₂ (max m₀ 1))
      rcases TCfg.exh_succ hW.1 with ⟨c₁, t, mt₁, F, hmv, hF, hFn, hx, he⟩ | hc | hn
      · exact absurd ⟨n, mt, mt₁, F, hW, hmv, hF, hFn, hx, he⟩
          (noOne _ (by omega) (c₁, t))
      · obtain ⟨δ, t₀, s₁, g, body, genv, hcall, hδ, vs, k, t, s₂, mt₁, hr, hmv, hx, he⟩ := hc
        refine ⟨_, Nat.le_max_left _ _, (δ, t₀, s₁, g, body, genv),
          hLκ _ _ _ _ _ _ hcall (agree (t := t₀) (mt₁ := t ++ mt₁) hW (he.trans (List.append_assoc _ _ _))),
          n, mt, hW, hcall, hδ, vs, k, t, s₂, mt₁, hr, hmv, hx, he⟩
      · have := hW.2.1
        omega
  obtain ⟨_, -, _, _, -, hcall, -⟩ := hκ 0
  let cg : TCfg d Mem unit := ⟨g, genv, body, { s₁ with mem := s₁.mem.enter }⟩
  obtain ⟨W, hpos, hW⟩ := M.exists_callBound
  by_cases hU : ∀ J m₁, ∃ m, m₁ ≤ m ∧ ∃ n mt vs k t s₂ mt₁, Wm m n mt ∧ δ ≤ n ∧
      Func.traceCall (Step (Act E Ans)) M (n - δ) g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s₂)) ∧
      mt = t₀ ++ t ++ mt₁ ∧ J < Step.ticks t
  · -- The callee's returns show unboundedly many steps: enter it.
    refine ⟨cg, t₀, δ + 1, hcall.enter, TGood.after fun k B => ?_⟩
    let D := kmax K (k + (Step.actsOf t₀).length)
    obtain ⟨m, hm, n, mt, vs, kr, t, s₂, mt₁, hWm, hδ, hx, rfl, hJ⟩ :=
      hU (W * (D + 1) + B) (k + (Step.actsOf t₀).length)
    have hpace := Func.traceCall_retPaced hone hx
    rcases Func.traceCall_cut_ret hone hW hpos (n := W * (D + 1) + B) (by omega) hx with
      ⟨hj, -⟩ | ⟨-, t₁, s₀, hp, ht₁, hb, he⟩
    · omega
    obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 he
    rcases e₁ with ⟨_, _⟩ | ⟨y, t₂, s₃⟩
    · cases he₁
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
    obtain ⟨rfl, rfl, -⟩ := he₁
    have hD : D < Step.ticks (t₀ ++ t₁) := by
      rw [Step.ticks_append]
      rcases hb with rfl | ⟨cc, hcc, hle⟩
      · omega
      have := hW _ _ hcc
      have hlt : W * (D + 1) < W * (Step.ticks t₁ + 1) := by
        rw [Nat.mul_succ W (Step.ticks t₁)]
        omega
      have := Nat.lt_of_mul_lt_mul_left hlt
      omega
    exact ⟨_, Nat.le_add_left _ _, t₁, ⟨s₃, h₁⟩, (hWm.2.2.mono hm).of_prefix
      ((List.prefix_append_right_inj t₀).2 hp |>.trans (List.prefix_append _ _)) hD⟩
  -- The callee's returns show at most `J` steps, from some `m₁` on.
  obtain ⟨J, hJ⟩ := Classical.not_forall.1 hU
  obtain ⟨m₁, hm₁⟩ := Classical.not_forall.1 hJ
  have hle : ∀ m n mt vs k t s₂ mt₁, m₁ ≤ m → Wm m n mt → δ ≤ n →
      Func.traceCall (Step (Act E Ans)) M (n - δ) g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s₂)) →
      mt = t₀ ++ t ++ mt₁ → Step.ticks t ≤ J := fun m n mt vs k t s₂ mt₁ h₁ hWm hδ hx he =>
    Nat.le_of_not_lt fun hlt => hm₁ ⟨m, h₁, n, mt, vs, k, t, s₂, mt₁, hWm, hδ, hx, he, hlt⟩
  let U₀ := W * J
  let ans₀ : Nat → Option Ans := fun i => ans ((Step.actsOf t₀).length + i)
  obtain ⟨C, hC⟩ := (ExceptStepFinite.inFrame (Func.traceOps_finite hfin M U₀ g genv body)) s₁ ans₀
  let Ret : Nat → Result (List (DVal d) × Nat) × List (Step (Act E Ans)) × TraceState Mem unit →
      Prop := fun m x =>
    ∃ n mt vs k t s₂ mt₁, Wm m n mt ∧ δ ≤ n ∧ U₀ ≤ n - δ ∧ n - δ - U₀ ≤ k ∧
      Func.traceCall (Step (Act E Ans)) M U₀ g genv body s₁
        (.ok (.ok (.ret (vs, k - (n - δ - U₀))), t, s₂)) ∧
      (∀ U k', Func.traceCall (Step (Act E Ans)) M U g genv body s₁
        (.ok (.ok (.ret (vs, k')), t, s₂)) →
        TCfg.Move (Act E Ans) M c (c.after vs s₂) (t₀ ++ t) (U + δ + 1)) ∧
      (c.after vs s₂).exh (Act E Ans) M (min k (n - δ)) mt₁ ∧ mt = t₀ ++ t ++ mt₁ ∧
      x = (.ret (vs, k - (n - δ - U₀)), t, s₂)
  obtain ⟨x, -, hx⟩ := List.exists_often_of_mem (L := C) (Q := Ret) fun m₂ => by
    obtain ⟨m, hm, n, mt, hWm, -, hδ, vs, k, t, s₂, mt₁, hr, hmv, hx, he⟩ :=
      hκ (max m₂ (max m₁ (U₀ + δ)))
    have hJt := hle _ n mt vs k t s₂ mt₁ (by omega) hWm hδ hr he
    have hfuel := Func.traceCall_retPaced_le hone hW hr
    have hU₀ : U₀ ≤ n - δ := by have := hWm.2.1; omega
    have hk : n - δ - U₀ ≤ k := by
      have : W * Step.ticks t ≤ U₀ := Nat.mul_le_mul_left _ hJt
      omega
    have hag := (Act.agrees_actsOf_append (agree (t := t₀ ++ t) (mt₁ := mt₁) hWm he)).2
    rcases Func.traceCall_cut_ret hone hW hpos hU₀ hr with ⟨-, hcut⟩ | ⟨hlt, -⟩
    · exact ⟨_, by omega, _, hC _ _ _ hcut hag,
        n, mt, vs, k, t, s₂, mt₁, hWm, hδ, hU₀, hk, hcut, hmv, hx, he, rfl⟩
    · omega
  obtain ⟨_, -, _, _, vs, k, t, s₂, _, -, -, -, -, hcut, hmv, -, -, rfl⟩ := hx 0
  refine ⟨c.after vs s₂, t₀ ++ t, U₀ + δ + 1, hmv _ _ hcut, TGood.after fun k' B => ?_⟩
  obtain ⟨m, hm, n, mt, vs', kk, t', s₂', mt₁, hWm, hδ, hU₀, hk, -, -, hx', rfl, hxe⟩ :=
    hx (k' + (Step.actsOf (t₀ ++ t)).length + B + U₀ + δ)
  simp only [Prod.mk.injEq, Result.ret.injEq] at hxe
  obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := hxe
  exact ⟨_, by have := hWm.2.1; omega, mt₁, hx', hWm.2.2.mono (by omega)⟩
end Fir
