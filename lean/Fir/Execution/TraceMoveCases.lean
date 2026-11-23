import Fir.Execution.TraceMoves
import Fir.Execution.TraceFiniteRuns

/-!
# The first move of a path

Each path of a configuration's run that runs out of fuel at a budget of at
least one goes on by a first move (`TCfg.exh_succ`):

* an op that runs by its own rule, or a call of an external declaration,
  with one of its outcomes, or a call that enters its callee whose path
  runs out of fuel: a move of one step of fuel, or of two when the rule of
  the call's op picks its callee (#235), after which the rest runs out of
  fuel at as many steps fewer;
* or a call whose callee returns: the configuration's first op calls a
  function of the module (`TCfg.Calls`), after the steps and acts of the
  rule that picks it, if any, and the path is the callee's return, then the
  rest, which runs out of fuel at the steps the callee leaves;
* or, with one step of fuel, the rule that picks a callee runs out of fuel.

`Fir.Execution.TraceMoveFinite` counts the moves of at most two steps of
fuel.
-/

namespace Fir

open Memory

variable {A : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {M : Module d}

/-- The configuration after a call of its first op returns the values `vs`
in the traced state `s₁`: the results bound, the rest of its ops to run. -/
def TCfg.after (c : TCfg d Mem unit) (vs : List (DVal d)) (s₁ : TraceState Mem unit) :
    TCfg d Mem unit :=
  match c.os with
  | o :: os => ⟨c.f, (o.results.map (·.1)).zip vs ++ c.env, os, s₁⟩
  | [] => c

variable [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))]

/-- The first op of the configuration calls the function `g` of the module
`M`, which it enters at the ops `body` with the environment `genv`, after
`δ` steps of fuel of its own and the acts `t₀`, from the traced state `s₁`:
none and from the configuration's state when the op names its callee, the
step and acts of the rule that picks it otherwise (#235). -/
def TCfg.Calls (M : Module d) (c : TCfg d Mem unit) (δ : Nat) (t₀ : List (Step A))
    (s₁ : TraceState Mem unit) (g : Func d) (body : List (Operation d)) (genv : Env d) : Prop :=
  ∃ o os, c.os = o :: os ∧ o.ownsCoreRegion = false ∧ isTerminator o.op = false ∧
    ∃ (args : HVector toType (sig o.op)) (sym : Name) (ts : List d.Ty) (cargs : HVector toType ts),
      c.env.operands (sig o.op) o.operands = .ok args ∧
      Func.TCallsAt M o args c.s δ sym ts cargs 0 t₀ s₁ ∧ M.func? sym = some g ∧
      g.enter cargs.toDVals = .ok (body, genv)

/-- A configuration whose first op calls a function enters it by a move. -/
theorem TCfg.Calls.enter {c : TCfg d Mem unit} {δ : Nat} {t₀ : List (Step A)}
    {s₁ : TraceState Mem unit} {g : Func d} {body : List (Operation d)} {genv : Env d}
    (h : c.Calls M δ t₀ s₁ g body genv) :
    TCfg.Move A M c ⟨g, genv, body, { s₁ with mem := s₁.mem.enter }⟩ t₀ (δ + 1) := by
  obtain ⟨o, os, hos, hreg, hT, args, sym, ts, cargs, hargs, hc, hg, hen⟩ := h
  rcases c with ⟨f, env, os', s⟩
  dsimp only at hos hargs hc
  subst hos
  exact .enter hreg hargs hT hc hg hen

/-- Each path of a configuration's run that runs out of fuel at a budget of
at least one goes on by a move of at most two steps of fuel, then runs out
of fuel at as many steps fewer; or the configuration's first op calls a
function of the module, which returns, after which the rest runs out of
fuel; or the budget is one and the rule that picks a callee runs out of
fuel. -/
theorem TCfg.exh_succ {c : TCfg d Mem unit} {n : Nat} {mt : List (Step A)}
    (h : c.exh A M (n + 1) mt) :
    (∃ c₁ t mt₁ F, TCfg.Move A M c c₁ t F ∧ F ≤ 2 ∧ F ≤ n + 1 ∧
      c₁.exh A M (n + 1 - F) mt₁ ∧ mt = t ++ mt₁) ∨
    (∃ δ t₀ s₁ g body genv, c.Calls M δ t₀ s₁ g body genv ∧ δ ≤ n ∧ ∃ vs k t s₂ mt₁,
      Func.traceCall (Step A) M (n - δ) g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s₂)) ∧
      (∀ U k', Func.traceCall (Step A) M U g genv body s₁ (.ok (.ok (.ret (vs, k')), t, s₂)) →
        TCfg.Move A M c (c.after vs s₂) (t₀ ++ t) (U + δ + 1)) ∧
      (c.after vs s₂).exh A M (min k (n - δ)) mt₁ ∧ mt = t₀ ++ t ++ mt₁) ∨
    n = 0 := by
  rcases c with ⟨f, env, os, s⟩
  obtain ⟨s₁, h⟩ := h
  match os, h with
  | [], h => exact absurd h (Func.traceOps_nil (TraceEnd.notStuck_ok _ _ _))
  | o :: os, h =>
    have hpath := (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).1 h
    generalize hE : (Except.ok (Except.ok Result.fuelExhausted, mt, s₁) :
      TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) = E
      at hpath
    have after : ∀ {e : TraceEnd (Step A) (TraceState Mem unit)
        (Except Stuck (Result (List (DVal d) × Nat)))} {t mt' : List (Step A)},
        .ok (.ok .fuelExhausted, mt', s₁) = TraceEnd.after t e →
        ∃ mt₁, e = .ok (.ok .fuelExhausted, mt₁, s₁) ∧ mt' = t ++ mt₁ := by
      intro e t mt' he
      rcases e with ⟨_, _⟩ | ⟨y, t', s'⟩
      · cases he
      · simp only [TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨t', rfl, rfl⟩
    -- The steps a call takes before its callee's.
    have norm : ∀ {args : HVector toType (sig o.op)} {sym : Name} {ts : List d.Ty}
        {cargs : HVector toType ts} {n' : Nat} {t₀ : List (Step A)} {s' : TraceState Mem unit},
        Func.TCallsAt M o args s n sym ts cargs n' t₀ s' →
        ∃ δ, n = n' + δ ∧ δ ≤ 1 ∧ Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s' :=
      fun {_ _ _ _ n' _ _} hc => ⟨n - n', by have := hc.le; omega, by have := hc.le; omega, by
        have := hc.at 0
        rwa [Nat.zero_add] at this⟩
    cases hpath with
    | exitUB => cases hE
    | ret => cases hE
    | denoteUB => cases hE
    | callUB => cases hE
    | extUB => cases hE
    | pickUB => cases hE
    | pickExh _ _ _ _ _ hn => exact .inr (.inr hn)
    | goto hreg hargs hT hos hx hj hr =>
      obtain ⟨mt₁, rfl, rfl⟩ := after hE
      exact .inl ⟨_, _, mt₁, 1, .goto hreg hargs hT hos hx hj, by omega, by omega,
        by rw [Nat.add_sub_cancel]; exact ⟨s₁, hr⟩, rfl⟩
    | denote hreg hargs hT hc hx hlen hr =>
      obtain ⟨mt₁, rfl, rfl⟩ := after hE
      exact .inl ⟨_, _, mt₁, 1, .denote hreg hargs hT hc hx hlen, by omega, by omega,
        by rw [Nat.add_sub_cancel]; exact ⟨s₁, hr⟩, rfl⟩
    | ext hreg hargs hT hc hg hd hx hty hlen hr =>
      obtain ⟨δ, hnδ, hδ, hc₀⟩ := norm hc
      obtain ⟨mt₂, he, rfl⟩ := after hE
      obtain ⟨mt₁, rfl, rfl⟩ := after he.symm
      refine .inl ⟨_, _, mt₁, δ + 1, .ext hreg hargs hT hc₀ hg hd hx hty hlen, by omega, by omega,
        ?_, (List.append_assoc _ _ _).symm⟩
      rw [show n + 1 - (δ + 1) = n - δ by omega, hnδ, Nat.add_sub_cancel]
      exact ⟨s₁, hr⟩
    | callExh hreg hargs hT hc hg hen hx =>
      obtain ⟨δ, hnδ, hδ, hc₀⟩ := norm hc
      obtain ⟨mt₁, he, rfl⟩ := after hE
      cases he
      obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 hx
      rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
      · cases he₁
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
      obtain ⟨rfl, rfl, -⟩ := he₁
      refine .inl ⟨_, _, _, δ + 1, .enter hreg hargs hT hc₀ hg hen, by omega, by omega, ?_, rfl⟩
      rw [show n + 1 - (δ + 1) = n - δ by omega, hnδ, Nat.add_sub_cancel]
      exact ⟨s₂, h₁⟩
    | @callRet args sym ts cargs n' t₀ s' g body genv vs k t s₂ e hreg hargs hT hc hg hen hx hty
        hlen hr =>
      obtain ⟨δ, rfl, hδ, hc₀⟩ := norm hc
      obtain ⟨mt₂, he, rfl⟩ := after hE
      obtain ⟨mt₁, rfl, rfl⟩ := after he.symm
      refine .inr (.inl ⟨δ, t₀, s', g, body, genv,
        ⟨o, os, rfl, hreg, hT, args, sym, ts, cargs, hargs, hc₀, hg, hen⟩, by omega, vs, k, t, s₂,
        mt₁, ?_, fun U k' hU => .ret hreg hargs hT hc₀ hg hen hU hty hlen, ?_,
        (List.append_assoc _ _ _).symm⟩)
      · rwa [Nat.add_sub_cancel]
      · rw [Nat.add_sub_cancel]
        exact ⟨_, hr⟩

end Fir
