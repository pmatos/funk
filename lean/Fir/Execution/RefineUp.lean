import Fir.Execution.BlackBox

/-!
# Every return and UB of the target, allowed

Let every call name the same function in both modules or a black box.
Let every op that runs by its own rule, a terminator or an op with no
callee, be monotone, among the ops of the source module's functions and
of the function that runs. Then every return and every UB of the
target's run of ops, from an environment that refines the source's, is
allowed by the source's run of the same ops at some budget. Calls and
recursion are included.

Monotonicity is asked only of the ops that the run can reach, not of
every op instance of the dialect. So a dialect whose ops are monotone
only at valid op instances meets it for every function of a valid module
(ADR-2026-11-05-1715), as the section on what the lawful class gives
proves.

The proof is by strong induction on the target's budget, for every
function at once, and follows the target's path by the ways a step goes
on. Its invariant is that the ops it runs are ops of the function that
runs, whose ops are monotone: the ops of one of its blocks, which a jump
keeps, as it goes to a block of the same function.

* An op's operands are found in the source's environment too, refined.
  What the op does on the target's operands is allowed by what it does on
  the source's: UB there allows anything; otherwise the source gives
  results that the target's refine, or goes to the same place. So the
  source's environment after the op is refined by the target's, and the
  induction covers the rest, with one step less.
* A call of the same function in both enters it at the same op, in
  environments of which the target's refines the source's, and the
  induction covers the callee, on fewer steps. The callee is a function
  of the source module, so its ops are monotone, and it starts at the ops
  of its entry block. A call of a black box is allowed by the black box's
  behaviours.
* When the source's callee returns, at one budget, values that the
  target's refine, and the rest of the source's run is allowed at
  another, the source's run is allowed at their sum plus one: its callee,
  with more steps, returns the same and leaves as many more, so its rest
  runs with at least the steps it needed, and does the same.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM] [TyRefinement d.Ty]

omit [DecidableEq d.Ty] in
/-- Every op of `os` that runs by its own rule, a terminator or an op
with no callee, is monotone. -/
def MonotoneOps (os : List (Operation d)) : Prop :=
  ∀ o ∈ os, isTerminator o.op = true ∨ callee? o.op = none → OpMonotone o.op

omit [DecidableEq d.Ty] in
/-- Every op of the function `f` that runs by its own rule is monotone. -/
def Func.OpsMonotone (f : Func d) : Prop :=
  ∀ b ∈ f.blocks, MonotoneOps b.body

/-- A run of `f` starts at the ops of one of its blocks. -/
theorem Func.OpsMonotone.enter {f : Func d} (hf : f.OpsMonotone) {dvs : List (DVal d)}
    {p : List (Operation d) × Env d} (hen : f.enter dvs = .ok p) : MonotoneOps p.1 := by
  obtain ⟨e, he, -, -, rfl⟩ := Func.enter_eq_ok hen
  exact hf e (List.mem_of_mem_head? he)

/-- A jump of `f` goes to the ops of one of its blocks. -/
theorem Func.OpsMonotone.jump {f : Func d} (hf : f.OpsMonotone) {env : Env d}
    {succs : List Succ} {i : Nat} {b : Block d} {env₁ : Env d}
    (hj : f.jump env succs i = .ok (b, env₁)) : MonotoneOps b.body := by
  obtain ⟨s, vs, -, hb, -⟩ := Func.jump_eq_ok hj
  exact hf b (Func.block?_some hb).1

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- UB at some budget allows every path. -/
theorem Allowed.of_someUB {src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    (h : SomeUB src) : ∀ e, Allowed src e
  | .ok (.ok (.ret _)) => .inl h
  | .ub _ => h
  | .ok (.ok .fuelExhausted) | .ok (.error _) => trivial

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- A path that runs out of fuel or is stuck is allowed by every source. -/
theorem Allowed.of_not {src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (h : ¬ (Ev.NotStuck e ∧ e ≠ .ok (.ok .fuelExhausted))) : Allowed src e := by
  match e with
  | .ok (.ok .fuelExhausted) | .ok (.error _) => trivial
  | .ok (.ok (.ret _)) => exact (h ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩).elim
  | .ub _ => exact (h ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩).elim

omit [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- A path allowed by the rest of a run is allowed by the whole, when every
way that the rest ends at the budget `N` is a way that the whole ends at
`N₀ + N + 1`, with `k` more steps left on a return. -/
theorem Allowed.of_step {src c : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))} (N₀ : Nat)
    (hstep : ∀ N x, Ev.NotStuck x → x ≠ .ok (.ok .fuelExhausted) → (c N).run x →
      (src (N₀ + N + 1)).run (x.addLeft k)) :
    Allowed c e → Allowed src e := by
  match e with
  | .ok (.ok .fuelExhausted) | .ok (.error _) => exact fun _ => trivial
  | .ub _ =>
    rintro ⟨N, r, h⟩
    exact ⟨_, r, hstep N (.ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩
  | .ok (.ok (.ret _)) =>
    rintro (⟨N, r, h⟩ | ⟨N, vs, i, h, hr⟩)
    · exact .inl ⟨_, r, hstep N (.ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩
    · exact .inr ⟨_, vs, i + k, hstep N (.ok (.ok (.ret (vs, i)))) (fun _ h => nomatch h)
        (fun h => nomatch h) h, hr⟩

/-- A return or UB of a call's callee in the target is allowed by the
source's callee: the same function, by the induction `ih`, or a black
box. The induction is asked only of a function of the source module,
whose ops are monotone, from the ops of its entry block. -/
theorem CallsRefined.callee_allowed {M M' : Module d} {bound : Nat} (hc : CallsRefined M M' bound)
    (hmono : ∀ g ∈ M.funcs, g.OpsMonotone) {s : Name} {g₀ : Func d} (hg' : M'.func? s = some g₀)
    {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {p' : List (Operation d) × Env d} (hen' : g₀.enter args'.toDVals = .ok p') {n : Nat}
    (ih : g₀.OpsMonotone → MonotoneOps p'.1 → ∀ (env env' : Env d), env.IsRefinedBy env' →
      ∀ e', (Func.runOps (m := SetM) M' n g₀ env' p'.1).run e' →
        Allowed (fun N => Func.runOps (m := SetM) M N g₀ env p'.1) e')
    {e' : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : (Func.runOps (m := SetM) M' n g₀ p'.2 p'.1).run e')
    (hne : Ev.NotStuck e') (hexh : e' ≠ .ok (.ok .fuelExhausted)) :
    ∃ g p, M.func? s = some g ∧ g.enter args.toDVals = .ok p ∧
      Allowed (fun N => Func.runOps (m := SetM) M N g p.2 p.1) e' := by
  rcases hc s with hsame | ⟨g, g', hg, hg'', bb⟩
  · obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    have hg : M.func? s = some g₀ := hsame ▸ hg'
    have hf := hmono g₀ (List.mem_of_find?_eq_some hg)
    exact ⟨g₀, (p'.1, genv), hg, hen, ih hf (hf.enter hen') genv p'.2 hgenv e' he'⟩
  · rw [hg''] at hg'
    cases hg'
    obtain ⟨p, hen, hm⟩ := bb.allowed hr hen' he' hne hexh
    exact ⟨g, p, hg, hen, hm⟩

/-- Every return and UB of the target's run of ops is allowed by the
source's at some budget, from environments of which the target's refines
the source's, when every call names the same function in both modules or
a black box, and every terminator and every op with no callee is
monotone, among the ops of the source module's functions, of the
function `f` that runs, and of the ops `os` it runs. -/
theorem Func.runOps_allowed {M M' : Module d} (hmono : ∀ g ∈ M.funcs, g.OpsMonotone)
    {bound : Nat} (hcalls : CallsRefined M M' bound) (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)), f.OpsMonotone →
      MonotoneOps os → env.IsRefinedBy env' →
      ∀ e', (Func.runOps (m := SetM) M' n f env' os).run e' →
        Allowed (fun N => Func.runOps (m := SetM) M N f env os) e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os hf hops henv e' he'
    classical
    by_cases hgood : Ev.NotStuck e' ∧ e' ≠ .ok (.ok .fuelExhausted)
    case neg => exact Allowed.of_not hgood
    obtain ⟨hne, hexh⟩ := hgood
    have hub : ∀ {N : Nat} {r : String} {o : Operation d} {os : List (Operation d)},
        Func.StepPath M N f env o os (.ub r) →
        (Func.runOps (m := SetM) M (N + 1) f env (o :: os)).run (.ub r) :=
      fun {_ r _ _} h => (Func.stepPath_iff (e := .ub r) (fun _ h => nomatch h)).2 h
    match n, os, hops, he' with
    | 0, _, _, he' => exact absurd (Func.run_runOps_zero.1 he') hexh
    | n + 1, [], _, he' => exact absurd he' (Func.run_runOps_nil hne)
    | n + 1, o :: os, hops, he' =>
      have ihn := ih n (Nat.lt_succ_self n)
      have hmo := hops o List.mem_cons_self
      have hops' : MonotoneOps os := fun o' h => hops o' (List.mem_cons_of_mem _ h)
      have step : ∀ {c : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))},
          (∀ N x, Ev.NotStuck x → (c N).run x → Func.StepPath M N f env o os x) →
          Allowed c e' → Allowed (fun N => Func.runOps (m := SetM) M N f env (o :: os)) e' :=
        fun hcp => Allowed.of_step (k := 0) 0 fun N x hx _ h => by
          rw [Nat.zero_add]
          match x, hx, h with
          | .ok (.ok (.ret (a, i))), hx, h => exact (Func.stepPath_iff hx).2 (hcp N _ hx h)
          | .ub r, hx, h => exact (Func.stepPath_iff hx).2 (hcp N _ hx h)
          | .ok (.ok .fuelExhausted), hx, h => exact (Func.stepPath_iff hx).2 (hcp N _ hx h)
          | .ok (.error st), hx, _ => exact absurd rfl (hx st)
      cases (Func.stepPath_iff hne).1 he' with
      | exitUB hreg hargs' hT hos hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact Allowed.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
      | ret hreg hargs' hT hos hx hs =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact Allowed.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok .ret, he₀, _ =>
          exact .inr ⟨1, _, 0, (Func.stepPath_iff (e := .ok (.ok (.ret (args.toDVals, 0))))
            (fun _ h => nomatch h)).2 (.ret hreg hargs hT hos he₀ hs),
            HVector.toDVals_isRefinedBy hr⟩
      | goto hreg hargs' hT hos hx hj he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact Allowed.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok (.goto _), he₀, rfl =>
          obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
          exact step (fun N x _ h => .goto hreg hargs hT hos he₀ hj₁ h)
            (ihn _ _ _ _ hf (hf.jump hj) henv₁ _ he)
      | denoteUB hreg hargs' hT hc hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact Allowed.of_someUB ⟨1, r, hub (.denoteUB hreg hargs hT hc he₀)⟩ _
      | denote hreg hargs' hT hc hx hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact Allowed.of_someUB ⟨1, r, hub (.denoteUB hreg hargs hT hc he₀)⟩ _
        | .ok rs, he₀, hrs =>
          have hvs := HVector.toDVals_isRefinedBy hrs
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          exact step (fun N x _ h => .denote hreg hargs hT hc he₀ hlen h)
            (ihn _ _ _ _ hf hops' (henv.zip_append _ hvs) _ he)
      | callUB hreg hargs' hT hc hg' hen' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hr (p' := (_, _)) hen'
          (fun hgm hbm env env' h e' he' => ihn _ env env' _ hgm hbm h e' he') hx
          (fun _ h => nomatch h) (fun h => nomatch h)
        obtain ⟨N, r, hN⟩ := hm
        exact Allowed.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen hN)⟩ _
      | callExh _ _ _ _ _ _ _ => exact absurd rfl hexh
      | callRet hreg hargs' hT hc hg' hen' hx hty' hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hr (p' := (_, _)) hen'
          (fun hgm hbm env env' h e' he' => ihn _ env env' _ hgm hbm h e' he') hx
          (fun _ h => nomatch h) (fun h => nomatch h)
        rcases hm with ⟨N, r, hN⟩ | ⟨N₁, vs, k, hx₁, hvs⟩
        · exact Allowed.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen hN)⟩ _
        have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
        have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
        have hm := ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _ _ hf hops'
          (henv.zip_append _ hvs) _ he
        exact Allowed.of_step N₁ (fun N₂ x hx hxe h =>
          Func.call_cont hreg hargs hT hc hg hen hx₁ hty hlen hx hxe h) hm

end Fir
