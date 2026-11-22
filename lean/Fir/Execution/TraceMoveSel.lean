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

* _Infinitely many go on by a move of one step of fuel._ There are finitely
  many such moves whose acts agree with the stream's answers
  (`TCfg.moves_one_finite`), so one is taken by infinitely many.
* _Otherwise the first op calls a function, and from some `m` on its callee
  returns_ (`TCfg.exh_succ_of_calls`).
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
  classical
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
    ∃ n mt mt₁, Wm m n mt ∧ TCfg.Move (Act E Ans) M c p.1 p.2 1 ∧ p.1.exh (Act E Ans) M n mt₁ ∧
      mt = p.2 ++ mt₁
  by_cases hI : ∀ m₀, ∃ m, m₀ ≤ m ∧ ∃ p, One m p
  · -- Infinitely many paths go on by a move of one step of fuel.
    obtain ⟨L, hL⟩ := TCfg.moves_one_finite (M := M) hfin c ans
    obtain ⟨⟨c₁, t⟩, -, hof⟩ := List.exists_often_of_mem (L := L) (Q := One) fun m₀ => by
      obtain ⟨m, hm, p, n, mt, mt₁, hW, hmv, hx, he⟩ := hI m₀
      exact ⟨m, hm, p, hL _ _ hmv (agree hW he), n, mt, mt₁, hW, hmv, hx, he⟩
    obtain ⟨_, -, _, _, _, -, hmv, -, -⟩ := hof 0
    refine ⟨c₁, t, 1, hmv, TGood.after fun k B => ?_⟩
    obtain ⟨m, hm, n, mt, mt₁, hW, -, hx, rfl⟩ := hof (k + (Step.actsOf t).length + B)
    exact ⟨n, by have := hW.2.1; omega, mt₁, hx, hW.2.2.mono (by omega)⟩
  -- From some `m₀` on, no path goes on by a move of one step of fuel.
  obtain ⟨m₀, hm₀⟩ := Classical.not_forall.1 hI
  have noOne : ∀ m, m₀ ≤ m → ∀ p, ¬ One m p := fun m hm p hp => hm₀ ⟨m, hm, p, hp⟩
  obtain ⟨n₀, mt₀, hW₀⟩ := hw m₀
  obtain ⟨g, body, genv, hcall⟩ : ∃ g body genv, c.Calls M g body genv := by
    rcases TCfg.exh_succ hW₀.1 with ⟨c₁, t, mt₁, hmv, hx, he⟩ | hc
    · exact absurd ⟨n₀, mt₀, mt₁, hW₀, hmv, hx, he⟩ (noOne m₀ (Nat.le_refl _) (c₁, t))
    · exact hc
  let cg : TCfg d Mem unit := ⟨g, genv, body, { c.s with mem := c.s.mem.enter }⟩
  -- Each later path is a return of the callee, then the rest.
  have hret : ∀ m n mt, m₀ ≤ m → Wm m n mt → ∃ vs k t s₁ mt₁,
      Func.traceCall (Step (Act E Ans)) M n g genv body c.s (.ok (.ok (.ret (vs, k)), t, s₁)) ∧
      (∀ U k', Func.traceCall (Step (Act E Ans)) M U g genv body c.s
        (.ok (.ok (.ret (vs, k')), t, s₁)) → TCfg.Move (Act E Ans) M c (c.after vs s₁) t (U + 1)) ∧
      (c.after vs s₁).exh (Act E Ans) M (min k n) mt₁ ∧ mt = t ++ mt₁ := fun m n mt hm hW => by
    rcases TCfg.exh_succ_of_calls hcall hW.1 with hx | hr
    · exact absurd ⟨n, mt, mt, hW, hcall.enter, hx, rfl⟩ (noOne m hm (cg, []))
    · exact hr
  obtain ⟨W, hpos, hW⟩ := M.exists_callBound
  by_cases hU : ∀ J m₁, ∃ m, m₁ ≤ m ∧ m₀ ≤ m ∧ ∃ n mt vs k t s₁ mt₁, Wm m n mt ∧
      Func.traceCall (Step (Act E Ans)) M n g genv body c.s (.ok (.ok (.ret (vs, k)), t, s₁)) ∧
      mt = t ++ mt₁ ∧ J < Step.ticks t
  · -- The callee's returns show unboundedly many steps: enter it.
    refine ⟨cg, [], 1, hcall.enter, TGood.after fun k B => ?_⟩
    let D := kmax K k
    obtain ⟨m, hm, -, n, mt, vs, kr, t, s₁, mt₁, hWm, hx, rfl, hJ⟩ := hU (W * (D + 1) + B) k
    have hpace := Func.traceCall_retPaced hone hx
    rcases Func.traceCall_cut_ret hone hW hpos (n := W * (D + 1) + B) (by omega) hx with
      ⟨hj, -⟩ | ⟨-, t₀, s₀, hp, ht₀, hb, he⟩
    · omega
    obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 he
    rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
    · cases he₁
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
    obtain ⟨rfl, rfl, -⟩ := he₁
    have hD : D < Step.ticks t₀ := by
      rcases hb with rfl | ⟨cc, hcc, hle⟩
      · omega
      have := hW _ _ hcc
      have hlt : W * (D + 1) < W * (Step.ticks t₀ + 1) := by
        rw [Nat.mul_succ W (Step.ticks t₀)]
        omega
      have := Nat.lt_of_mul_lt_mul_left hlt
      omega
    exact ⟨_, Nat.le_add_left _ _, t₀, ⟨s₂, h₁⟩,
      (hWm.2.2.mono hm).of_prefix (hp.trans (List.prefix_append _ _)) hD⟩
  -- The callee's returns show at most `J` steps, from some `m₁` on.
  obtain ⟨J, hJ⟩ := Classical.not_forall.1 hU
  obtain ⟨m₁, hm₁⟩ := Classical.not_forall.1 hJ
  have hle : ∀ m n mt vs k t s₁ mt₁, m₁ ≤ m → m₀ ≤ m → Wm m n mt →
      Func.traceCall (Step (Act E Ans)) M n g genv body c.s (.ok (.ok (.ret (vs, k)), t, s₁)) →
      mt = t ++ mt₁ → Step.ticks t ≤ J := fun m n mt vs k t s₁ mt₁ h₁ h₀ hWm hx he =>
    Nat.le_of_not_lt fun hlt => hm₁ ⟨m, h₁, h₀, n, mt, vs, k, t, s₁, mt₁, hWm, hx, he, hlt⟩
  let U₀ := W * J
  obtain ⟨C, hC⟩ := (ExceptStepFinite.inFrame (Func.traceOps_finite hfin M U₀ g genv body)) c.s ans
  let Ret : Nat → Result (List (DVal d) × Nat) × List (Step (Act E Ans)) × TraceState Mem unit →
      Prop := fun m x =>
    ∃ n mt vs k t s₁ mt₁, Wm m n mt ∧ U₀ ≤ n ∧ n - U₀ ≤ k ∧
      Func.traceCall (Step (Act E Ans)) M U₀ g genv body c.s
        (.ok (.ok (.ret (vs, k - (n - U₀))), t, s₁)) ∧
      (∀ U k', Func.traceCall (Step (Act E Ans)) M U g genv body c.s
        (.ok (.ok (.ret (vs, k')), t, s₁)) → TCfg.Move (Act E Ans) M c (c.after vs s₁) t (U + 1)) ∧
      (c.after vs s₁).exh (Act E Ans) M (min k n) mt₁ ∧ mt = t ++ mt₁ ∧
      x = (.ret (vs, k - (n - U₀)), t, s₁)
  obtain ⟨x, -, hx⟩ := List.exists_often_of_mem (L := C) (Q := Ret) fun m₂ => by
    obtain ⟨n, mt, hWm⟩ := hw (max m₂ (max m₀ (max m₁ U₀)))
    have hm := Nat.le_refl (max m₂ (max m₀ (max m₁ U₀)))
    obtain ⟨vs, k, t, s₁, mt₁, hr, hmv, hx, he⟩ :=
      hret _ n mt (by omega) hWm
    have hJt := hle _ n mt vs k t s₁ mt₁ (by omega) (by omega) hWm hr he
    have hfuel := Func.traceCall_retPaced_le hone hW hr
    have hU₀ : U₀ ≤ n := by have := hWm.2.1; omega
    have hk : n - U₀ ≤ k := by
      have : W * Step.ticks t ≤ U₀ := Nat.mul_le_mul_left _ hJt
      omega
    rcases Func.traceCall_cut_ret hone hW hpos hU₀ hr with ⟨-, hcut⟩ | ⟨hlt, -⟩
    · exact ⟨_, Nat.le_max_left _ _, _, hC _ _ _ hcut (agree hWm he),
        n, mt, vs, k, t, s₁, mt₁, hWm, hU₀, hk, hcut, hmv, hx, he, rfl⟩
    · omega
  obtain ⟨_, -, _, _, vs, k, t, s₁, _, -, -, -, hcut, hmv, -, -, rfl⟩ := hx 0
  refine ⟨c.after vs s₁, t, U₀ + 1, hmv _ _ hcut, TGood.after fun k' B => ?_⟩
  obtain ⟨m, hm, n, mt, vs', kk, t', s₁', mt₁, hWm, hU₀, hk, -, -, hx', rfl, hxe⟩ :=
    hx (k' + (Step.actsOf t).length + B + U₀)
  simp only [Prod.mk.injEq, Result.ret.injEq] at hxe
  obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := hxe
  exact ⟨_, by have := hWm.2.1; omega, mt₁, hx', hWm.2.2.mono (by omega)⟩

end Fir
