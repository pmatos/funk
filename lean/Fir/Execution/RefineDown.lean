import Fir.Execution.RefineUp

/-!
# Divergence of the target, allowed

A target that diverges runs out of fuel at every budget, and the source
must then diverge too, or hit UB at some budget. The previous section
cannot show it: a path that runs out of fuel holds no value to follow,
and a black box's target may spend its steps in a callee that the source
runs in one. So this section relates budgets. With `B = bound + 1`, a path
of the target's run of ops at a budget `n` of at least `B * (N + 1)` that
runs out of fuel or returns is allowed by the source at the budget `N`
(`AllowedBelow`, `Func.runOps_allowedBelow`): the source runs out of fuel
at `N`, or hits UB at some budget, or, on a return, returns at `N` values
that the target's refine, and leaves at most a `B`th of the steps that
the target leaves.

The proof is by strong induction on the target's budget. Each op takes
one step in both runs, a call of the same function included, whose callee
the induction covers. A black-box call is where the budgets part
(`BlackBox.allowedBelow`):

* If its target diverges on the call's arguments, the black box gives
  that its source diverges on the source's, or hits UB. So the source's
  callee runs out of fuel at any budget, or hits UB at some budget.
* Otherwise none of its target's runs with `bound` steps or more runs out
  of fuel, so a run of it that returns takes at most `bound` steps: with
  the call's own step, at most `B` steps of the target for the source's
  one or more. The source's callee runs out of fuel at its budget, or,
  by fuel monotonicity, returns at it what the black box allows.

So a path of the target with `B` steps for each of the source's reaches a
point where the source runs out of fuel or hits UB, or keeps that ratio
to its end.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM] [TyRefinement d.Ty]

/-- The source `src` at the budget `N` allows the target's path that runs
out of fuel or returns: it runs out of fuel at `N`, or hits UB at some
budget, or, on a return, it returns at `N` values that the target's
refine, and leaves at most a `B`th of the steps that the target leaves.
A path that hits UB or is stuck asks nothing here. -/
def AllowedBelow (B : Nat) (src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat)))
    (N : Nat) : Ev (Except Stuck (Result (List (DVal d) × Nat))) → Prop
  | .ok (.ok .fuelExhausted) => (src N).run (.ok (.ok .fuelExhausted)) ∨ SomeUB src
  | .ok (.ok (.ret (vs', k'))) => (src N).run (.ok (.ok .fuelExhausted)) ∨ SomeUB src ∨
    ∃ vs k, (src N).run (.ok (.ok (.ret (vs, k)))) ∧ vs ⊑ vs' ∧ B * (k + 1) ≤ k'
  | _ => True

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- UB at some budget allows every path. -/
theorem AllowedBelow.of_someUB {B N : Nat}
    {src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))} (h : SomeUB src) :
    ∀ e, AllowedBelow B src N e
  | .ok (.ok .fuelExhausted) => .inr h
  | .ok (.ok (.ret _)) => .inr (.inl h)
  | .ub _ | .ok (.error _) => trivial

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- Running out of fuel at `N` allows every path. -/
theorem AllowedBelow.of_exhausted {B N : Nat}
    {src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    (h : (src N).run (.ok (.ok .fuelExhausted))) : ∀ e, AllowedBelow B src N e
  | .ok (.ok .fuelExhausted) => .inl h
  | .ok (.ok (.ret _)) => .inl h
  | .ub _ | .ok (.error _) => trivial

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- A path allowed by the rest of a run at the budget `N` is allowed by
the whole at `N'`, when every way that the rest ends at `N` is a way that
the whole ends at `N'`, and UB of the rest at some budget is UB of the
whole at some budget. -/
theorem AllowedBelow.of_step {B N N' : Nat}
    {src c : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (hstep : ∀ x, Ev.NotStuck x → (c N).run x → (src N').run x)
    (hub : SomeUB c → SomeUB src) : AllowedBelow B c N e → AllowedBelow B src N' e := by
  match e with
  | .ub _ | .ok (.error _) => exact fun _ => trivial
  | .ok (.ok .fuelExhausted) =>
    rintro (h | h)
    · exact .inl (hstep _ (fun _ h => nomatch h) h)
    · exact .inr (hub h)
  | .ok (.ok (.ret _)) =>
    rintro (h | h | ⟨vs, k, h, hr, hk⟩)
    · exact .inl (hstep _ (fun _ h => nomatch h) h)
    · exact .inr (.inl (hub h))
    · exact .inr (.inr ⟨vs, k, hstep (.ok (.ok (.ret (vs, k)))) (fun _ h => nomatch h) h, hr, hk⟩)

/-- A path of a black box's target that runs out of fuel or returns, called
on arguments that refine the source's at a budget `n` of at least
`bound + (bound + 1) * (N₀ + 1)`, is allowed by the source's callee at
`N₀`, which starts. -/
theorem BlackBox.allowedBelow {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : BlackBox M M' bound g g') {ts : List d.Ty} {args args' : HVector toType ts}
    (hr : args.Forall₂ TyRefinement.IsRefinedBy args') {n N₀ : Nat}
    (hn : bound + (bound + 1) * (N₀ + 1) ≤ n) {p' : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p')
    {e' : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : (Func.runOps (m := SetM) M' n g' p'.2 p'.1).run e')
    (hne : Ev.NotStuck e') (hub : ∀ r, e' ≠ .ub r) :
    ∃ p, g.enter args.toDVals = .ok p ∧
      AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N g p.2 p.1) N₀ e' := by
  have hsig := bb.sig hen'
  have hen'' : g'.enter ((args'.cast hsig).cast bb.params.symm).toDVals = .ok p' := by
    rw [HVector.toDVals_cast, HVector.toDVals_cast]; exact hen'
  have href := bb.refines _ _ (HVector.forall₂_cast hsig hr)
  have hcast : (args.cast hsig).toDVals = args.toDVals := HVector.toDVals_cast _ _
  have ofUB : ∀ {N : Nat} {r : String}, (g.runs M (args.cast hsig) N).outcomes (.ub r) →
      ∃ p, g.enter args.toDVals = .ok p ∧
        AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N g p.2 p.1) N₀ e' := by
    intro N r h
    obtain ⟨p, hp, hx⟩ := Func.runs_ub_inv h
    exact ⟨p, hcast ▸ hp, AllowedBelow.of_someUB ⟨N, r, hx⟩ _⟩
  have ofExh : (g.runs M (args.cast hsig) N₀).outcomes .fuelExhausted →
      ∃ p, g.enter args.toDVals = .ok p ∧
        AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N g p.2 p.1) N₀ e' := by
    intro h
    obtain ⟨p, hp, hx⟩ := Func.runs_exh_inv h
    exact ⟨p, hcast ▸ hp, AllowedBelow.of_exhausted hx _⟩
  rcases bb.bounded ((args'.cast hsig).cast bb.params.symm) with hdiv | hbdd
  · obtain ⟨s₀, hs₀, hle⟩ := href .fuelExhausted hdiv
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ofUB hN
    | .fuelExhausted, hs₀, _ => exact ofExh (hs₀ N₀)
    | .ret _, _, hle => exact hle.elim
  have hbn : bound ≤ n := by omega
  match e', he', hne, hub with
  | .ok (.ok .fuelExhausted), he', _, _ =>
    exact absurd (Func.runs_of_runOps hen'' he') (hbdd n hbn)
  | .ok (.ok (.ret (vs', k'))), he', _, _ =>
    have hk' : n - bound ≤ k' := by
      have ha := Func.runOps_ahead M' bound (n - bound) g' p'.2 p'.1
      rw [Nat.add_sub_cancel' hbn] at ha
      rcases ha.down_ret _ _ he' with ⟨h, _⟩ | h
      · exact h
      · exact absurd (Func.runs_of_runOps hen'' h) (hbdd bound (Nat.le_refl _))
    obtain ⟨s₀, hs₀, hle⟩ := href (.ret vs') ⟨n, Func.runs_of_runOps hen'' he'⟩
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ofUB hN
    | .fuelExhausted, _, hle => exact hle.elim
    | .ret vs, ⟨N₁, hN₁⟩, hvs =>
      by_cases hex : (g.runs M (args.cast hsig) N₀).outcomes .fuelExhausted
      · exact ofExh hex
      have hfm := Func.fuelMonotone M g (args.cast hsig)
      have hret : (g.runs M (args.cast hsig) N₀).outcomes (.ret vs) := by
        rcases Nat.le_total N₁ N₀ with h | h
        · exact hfm.up (o := .ret vs) h (fun h => nomatch h) hN₁
        · exact (hfm.down (o := .ret vs) h (fun h => nomatch h) hN₁).resolve_right hex
      obtain ⟨p, hp, k, hx⟩ := Func.runs_ret_inv hret
      have hk := Func.runOps_left_le M N₀ g p.2 p.1 vs k hx
      have hmul : (bound + 1) * (k + 1) ≤ (bound + 1) * (N₀ + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_succ hk)
      exact ⟨p, hcast ▸ hp, .inr (.inr ⟨vs, k, hx, hvs, by omega⟩)⟩
  | .ub r, _, _, hub => exact absurd rfl (hub r)
  | .ok (.error st), _, hne, _ => exact absurd rfl (hne st)

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- A path that hits UB or is stuck is allowed by every source. -/
theorem AllowedBelow.of_not {B N : Nat}
    {src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (h : ¬ (Ev.NotStuck e ∧ ∀ r, e ≠ .ub r)) : AllowedBelow B src N e := by
  match e with
  | .ub _ | .ok (.error _) => trivial
  | .ok (.ok .fuelExhausted) | .ok (.ok (.ret _)) =>
    exact (h ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩).elim

/-- A path of a call's callee in the target that runs out of fuel or
returns is allowed at `N₀` by the source's callee: the same function, by
the induction `ih`, or a black box. -/
theorem CallsRefined.callee_allowedBelow {M M' : Module d} {bound : Nat}
    (hc : CallsRefined M M' bound)
    {s : Name} {g₀ : Func d} (hg' : M'.func? s = some g₀) {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {p' : List (Operation d) × Env d} (hen' : g₀.enter args'.toDVals = .ok p') {n N₀ : Nat}
    (hn : bound + (bound + 1) * (N₀ + 1) ≤ n)
    (ih : ∀ (env env' : Env d), env.IsRefinedBy env' → ∀ e',
      (Func.runOps (m := SetM) M' n g₀ env' p'.1).run e' →
        AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N g₀ env p'.1) N₀ e')
    {e' : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : (Func.runOps (m := SetM) M' n g₀ p'.2 p'.1).run e')
    (hne : Ev.NotStuck e') (hub : ∀ r, e' ≠ .ub r) :
    ∃ g p, M.func? s = some g ∧ g.enter args.toDVals = .ok p ∧
      AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N g p.2 p.1) N₀ e' := by
  rcases hc s with hsame | ⟨g, g', hg, hg'', bb⟩
  · obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    exact ⟨g₀, (p'.1, genv), hsame ▸ hg', hen, ih genv p'.2 hgenv e' he'⟩
  · rw [hg''] at hg'
    cases hg'
    obtain ⟨p, hen, hm⟩ := bb.allowedBelow hr hn hen' he' hne hub
    exact ⟨g, p, hg, hen, hm⟩

/-- Every path of the target's run of ops that runs out of fuel or
returns, at a budget of at least `(bound + 1) * (N + 1)`, is allowed by
the source's run at `N`, from environments of which the target's refines
the source's, when every terminator and every op with no callee is
monotone, and every call names the same function in both modules or a
black box. -/
theorem Func.runOps_allowedBelow
    (hmono : ∀ op : d.Op, isTerminator op = true ∨ callee? op = none → OpMonotone op)
    {M M' : Module d} {bound : Nat} (hcalls : CallsRefined M M' bound) (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (N : Nat),
      env.IsRefinedBy env' → (bound + 1) * (N + 1) ≤ n →
      ∀ e', (Func.runOps (m := SetM) M' n f env' os).run e' →
        AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N f env os) N e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os N henv hN e' he'
    by_cases hgood : Ev.NotStuck e' ∧ ∀ r, e' ≠ .ub r
    case neg => exact AllowedBelow.of_not hgood
    obtain ⟨hne, hnub⟩ := hgood
    have hpos : 0 < (bound + 1) * (N + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have hub : ∀ {N : Nat} {r : String} {o : Operation d} {os : List (Operation d)},
        Func.StepPath M N f env o os (.ub r) →
        (Func.runOps (m := SetM) M (N + 1) f env (o :: os)).run (.ub r) :=
      fun {_ r _ _} h => (Func.stepPath_iff (e := .ub r) (fun _ h => nomatch h)).2 h
    match n, os, N, he' with
    | 0, _, _, _ => omega
    | _ + 1, _, 0, _ => exact AllowedBelow.of_exhausted (Func.run_runOps_zero.2 rfl) _
    | n + 1, [], _ + 1, he' => exact absurd he' (Func.run_runOps_nil hne)
    | n + 1, o :: os, N₀ + 1, he' =>
      have hb : bound + (bound + 1) * (N₀ + 1) ≤ n := by rw [Nat.mul_succ] at hN; omega
      have hb' : (bound + 1) * (N₀ + 1) ≤ n := by omega
      have ihn := ih n (Nat.lt_succ_self n)
      have step : ∀ {c : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))},
          (∀ N x, Ev.NotStuck x → (c N).run x → Func.StepPath M N f env o os x) →
          AllowedBelow (bound + 1) c N₀ e' →
          AllowedBelow (bound + 1) (fun N => Func.runOps (m := SetM) M N f env (o :: os))
            (N₀ + 1) e' :=
        fun hcp => AllowedBelow.of_step (fun x hx h => (Func.stepPath_iff hx).2 (hcp _ x hx h))
          (fun ⟨N, r, h⟩ => ⟨N + 1, r, hub (hcp N _ (fun _ h => nomatch h) h)⟩)
      cases (Func.stepPath_iff hne).1 he' with
      | exitUB _ _ _ _ _ => exact absurd rfl (hnub _)
      | denoteUB _ _ _ _ _ => exact absurd rfl (hnub _)
      | callUB _ _ _ _ _ _ _ => exact absurd rfl (hnub _)
      | ret hreg hargs' hT hos hx hs =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmono o.op (.inl hT) args _ hr).2 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact AllowedBelow.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok .ret, he₀, _ =>
          exact .inr (.inr ⟨_, N₀, (Func.stepPath_iff (e := .ok (.ok (.ret (args.toDVals, N₀))))
            (fun _ h => nomatch h)).2 (.ret hreg hargs hT hos he₀ hs),
            HVector.toDVals_isRefinedBy hr, hb'⟩)
      | goto hreg hargs' hT hos hx hj he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmono o.op (.inl hT) args _ hr).2 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact AllowedBelow.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok (.goto _), he₀, rfl =>
          obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
          exact step (fun N x _ h => .goto hreg hargs hT hos he₀ hj₁ h)
            (ihn _ _ _ _ _ henv₁ hb' _ he)
      | denote hreg hargs' hT hc hx hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmono o.op (.inr hc) args _ hr).1 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact AllowedBelow.of_someUB ⟨1, r, hub (.denoteUB hreg hargs hT hc he₀)⟩ _
        | .ok rs, he₀, hrs =>
          have hvs := HVector.toDVals_isRefinedBy hrs
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          exact step (fun N x _ h => .denote hreg hargs hT hc he₀ hlen h)
            (ihn _ _ _ _ _ (henv.zip_append _ hvs) hb' _ he)
      | callExh hreg hargs' hT hc hg' hen' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowedBelow hg' hr (p' := (_, _)) hen' hb
          (fun env env' h e' he' => ihn _ env env' _ N₀ h hb' e' he') hx (fun _ h => nomatch h)
          (fun _ h => nomatch h)
        rcases hm with h | ⟨N, r, h⟩
        · exact AllowedBelow.of_exhausted ((Func.stepPath_iff (e := .ok (.ok .fuelExhausted))
            (fun _ h => nomatch h)).2 (.callExh hreg hargs hT hc hg hen h)) _
        · exact AllowedBelow.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen h)⟩ _
      | callRet hreg hargs' hT hc hg' hen' hx hty' hlen' he =>
        rename_i vs' k'
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowedBelow hg' hr (p' := (_, _)) hen' hb
          (fun env env' h e' he' => ihn _ env env' _ N₀ h hb' e' he') hx (fun _ h => nomatch h)
          (fun _ h => nomatch h)
        rcases hm with h | ⟨N, r, h⟩ | ⟨vs, k, hx₁, hvs, hk⟩
        · exact AllowedBelow.of_exhausted ((Func.stepPath_iff (e := .ok (.ok .fuelExhausted))
            (fun _ h => nomatch h)).2 (.callExh hreg hargs hT hc hg hen h)) _
        · exact AllowedBelow.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen h)⟩ _
        have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
        have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
        have hk'n := Func.runOps_left_le M' n _ _ _ _ _ hx
        have hkN := Func.runOps_left_le M N₀ _ _ _ _ _ hx₁
        rw [Nat.min_eq_left hk'n] at he
        have hm := ih k' (Nat.lt_succ_of_le hk'n) _ _ _ _ k (henv.zip_append _ hvs) hk _ he
        refine AllowedBelow.of_step (fun x hx h => (Func.stepPath_iff hx).2
          (.callRet hreg hargs hT hc hg hen hx₁ hty hlen (by rwa [Nat.min_eq_left hkN]))) ?_ hm
        rintro ⟨N₂, r, h⟩
        exact ⟨_, r, Func.call_cont hreg hargs hT hc hg hen hx₁ hty hlen
          (x := .ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩

end Fir
