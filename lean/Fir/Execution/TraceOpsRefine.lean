import Fir.Execution.TraceStepPaths

/-!
# A traced run of ops on environments and states that refine others

Let every op that runs by its own rule, a terminator or an op with no
callee, be monotone in the traced layer, among the ops of the module's
functions and of the function that runs. Then, at every budget, every path
of a traced run of ops that is not stuck, from an environment and a traced
state that refine others, is allowed by a path of the run of the same ops
from those others, at the same budget. Calls and recursion are included.

The two runs go in step: they run the same ops of the same module, each op
takes one step of fuel in both, and a callee's return leaves the same steps
in both. So the source's path:

* returns values that the target's refine, with the same steps left, after
  acts that the target's refine one by one, in a traced state that the
  target's refines; or
* runs out of fuel after acts that the target's refine one by one, in a
  traced state that the target's refines; or
* hits UB after acts that the target first shows, refined.

The proof follows the ways a step goes on, by strong induction on the
budget, for every function at once and from every traced state:

* An op's operands are found in the source's environment too, refined, and
  it starts from a traced state that the target's refines. What it does in
  the target is allowed by what it does in the source: UB after the acts
  _t_, which allows anything that first shows acts refining _t_; or results
  that the target's refine, or the same place to go, after acts that the
  target's refine, with a traced state that the target's refines. The
  induction covers the rest of the run, after those acts.
* A call enters the same function in both, in environments of which the
  target's refines the source's, from traced states with a frame entered,
  of which the target's refines the source's too; the induction covers the
  callee. Leaving a frame keeps refinement. When the callee returns, the
  rest of the run goes on with the same steps left in both.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {B : Type} [HRefinement B B]
  {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty]

/-- What a path of a source's run of ops ends with allows what a path of the
target's run ends with, in step: a return allows a return of values that
refine its own, with the same steps left, and running out of fuel allows
running out of fuel. -/
def Result.InStep : Except Stuck (Result (List (DVal d) × Nat)) →
    Except Stuck (Result (List (DVal d) × Nat)) → Prop
  | .ok (.ret (vs, k)), .ok (.ret (vs', k')) => vs ⊑ vs' ∧ k = k'
  | .ok .fuelExhausted, .ok .fuelExhausted => True
  | _, _ => False

/-- Leaving a frame keeps a way of ending allowing another. -/
theorem TraceEnd.Allows.exitFrame {γ γ' : Type} {r : γ → γ' → Prop} :
    ∀ {e : TraceEnd B (TraceState Mem unit) γ} {e' : TraceEnd B (TraceState Mem unit) γ'},
      TraceEnd.Allows r e e' →
      TraceEnd.Allows r (e.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit }))
        (e'.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit }))
  | .ok _, .ok _, h => ⟨h.1, h.2.1, TraceState.IsRefinedBy.exit h.2.2⟩
  | .error _, .ok _, h => h
  | .error _, .error _, h => h
  | .ok _, .error _, h => h.elim

/-- UB after the acts `t` of an op, then the source's path ends there, allows
every way the target goes on after acts refining `t`'s. -/
theorem TraceEnd.Allows.ub_prefix {r : String} {t t' : List B}
    (h : List.IsRefinedPrefix t t')
    (e' : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) :
    TraceEnd.Allows Result.InStep (.error (r, t)) (e'.after t') := by
  show List.IsRefinedPrefix t (e'.after t').trace
  rw [TraceEnd.trace_after]
  exact h.append_right _

variable [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))]

/-- The way a call's callee ends, in its frame, in the target is allowed by a
way it ends in the source, when the callee's run of ops from a traced state
with a frame entered is. -/
theorem Func.traceCall_allowed {M : Module d} {n : Nat} {g : Func d} {genv genv' : Env d}
    {body : List (Operation d)} {s s' : TraceState Mem unit}
    (h : ∀ e', Func.traceOps B M n g genv' body { s' with mem := s'.mem.enter } e' →
      TraceEnd.NotStuck e' → ∃ e, Func.traceOps B M n g genv body { s with mem := s.mem.enter } e ∧
        TraceEnd.Allows Result.InStep e e')
    {e' : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : Func.traceCall B M n g genv' body s' e') (hne : TraceEnd.NotStuck e') :
    ∃ e, Func.traceCall B M n g genv body s e ∧ TraceEnd.Allows Result.InStep e e' := by
  obtain ⟨e₁', he₁', rfl⟩ := (TraceM.run_inFrame _ _ _).1 he'
  have hne₁ : TraceEnd.NotStuck e₁' := by
    rintro st t s₁ rfl
    exact hne st t _ rfl
  obtain ⟨e₁, he₁, hle⟩ := h e₁' he₁' hne₁
  exact ⟨_, (TraceM.run_inFrame _ _ _).2 ⟨e₁, he₁, rfl⟩, hle.exitFrame⟩

/-- At every budget, every path of the target's traced run of ops that is not
stuck is allowed, in step, by a path of the source's run of the same ops at
the same budget, from environments and traced states of which the target's
refine the source's, when every terminator and every op with no callee is
monotone in the traced layer, among the ops of the module's functions, of
the function `f` that runs, and of the ops `os` it runs. -/
theorem Func.traceOps_allowed {M : Module d}
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone B (TraceState Mem unit)) (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (s s' : TraceState Mem unit),
      f.TraceOpsMonotone B (TraceState Mem unit) → TraceMonotoneOps B (TraceState Mem unit) os →
      env.IsRefinedBy env' → s ⊑ s' →
      ∀ e', Func.traceOps B M n f env' os s' e' → TraceEnd.NotStuck e' →
        ∃ e, Func.traceOps B M n f env os s e ∧ TraceEnd.Allows Result.InStep e e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os s s' hf hops henv hS e' he' hne
    match n, os, hops, he' with
    | 0, _, _, he' =>
      cases Func.traceOps_zero.1 he'
      exact ⟨_, Func.traceOps_zero.2 rfl, trivial, trivial, hS⟩
    | n + 1, [], _, he' => exact absurd he' (Func.traceOps_nil hne)
    | n + 1, o :: os, hops, he' =>
      have ihn := ih n (Nat.lt_succ_self n)
      have hmo := hops o List.mem_cons_self
      have hops' : TraceMonotoneOps B (TraceState Mem unit) os :=
        fun o' h => hops o' (List.mem_cons_of_mem _ h)
      have src : ∀ {x}, TraceEnd.NotStuck x → Func.TStepPath M n f env o os s x →
          Func.traceOps B M (n + 1) f env (o :: os) s x :=
        fun hx h => (Func.tStepPath_iff hx).2 h
      have ub : ∀ {r : String} {t : List B}, Func.TStepPath M n f env o os s (.error (r, t)) →
          Func.traceOps B M (n + 1) f env (o :: os) s (.error (r, t)) :=
        fun h => src (TraceEnd.notStuck_error _ _) h
      have callee : ∀ {args' : HVector toType (sig o.op)} {sym : Name} {g : Func d}
          {body : List (Operation d)} {genv' : Env d} {e₁'},
          env'.operands (sig o.op) o.operands = .ok args' → M.func? sym = some g →
          g.enter args'.toDVals = .ok (body, genv') → Func.traceCall B M n g genv' body s' e₁' →
          TraceEnd.NotStuck e₁' → ∃ (args : HVector toType (sig o.op)) (genv : Env d) (e₀ : _),
            env.operands (sig o.op) o.operands = .ok args ∧ g.enter args.toDVals = .ok (body, genv) ∧
            Func.traceCall B M n g genv body s e₀ ∧ TraceEnd.Allows Result.InStep e₀ e₁' := by
        intro args' sym g body genv' e₁' hargs' hg hen' hx hne₁
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
        have hgm := hmono _ (List.mem_of_find?_eq_some hg)
        obtain ⟨e₀, he₀, hle⟩ := Func.traceCall_allowed (fun e₂' he₂' hne₂ =>
          ihn _ genv _ _ _ _ hgm (hgm.enter hen') hgenv (TraceState.IsRefinedBy.enter hS) e₂' he₂'
            hne₂) hx hne₁
        exact ⟨args, genv, e₀, hargs, hen, he₀, hle⟩
      cases (Func.tStepPath_iff hne).1 he' with
      | exitUB hreg hargs' hT hos hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact ⟨_, ub (.exitUB hreg hargs hT hos he₀), hle⟩
        · exact hle.elim
      | ret hreg hargs' hT hos hx hs =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨x, t₀, s₀⟩
        · exact ⟨_, ub (.exitUB hreg hargs hT hos he₀), hle⟩
        · obtain ⟨rfl, ht, hs₀⟩ := hle
          exact ⟨_, src (TraceEnd.notStuck_ok _ _ _) (.ret hreg hargs hT hos he₀ hs),
            ⟨HVector.toDVals_isRefinedBy hr, rfl⟩, ht, hs₀⟩
      | goto hreg hargs' hT hos hx hj he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨x, t₀, s₀⟩
        · exact ⟨_, ub (.exitUB hreg hargs hT hos he₀), TraceEnd.Allows.ub_prefix hle _⟩
        · obtain ⟨rfl, ht, hs₀⟩ := hle
          obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
          obtain ⟨e₁, he₁, hle₁⟩ := ihn f env₁ _ _ s₀ _ hf (hf.jump hj₁) henv₁ hs₀ _ he
            (TraceEnd.NotStuck.of_after hne)
          exact ⟨_, src ((hle₁.after ht).notStuck fun _ _ h => h) (.goto hreg hargs hT hos he₀ hj₁ he₁),
            hle₁.after ht⟩
      | denoteUB hreg hargs' hT hc hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact ⟨_, ub (.denoteUB hreg hargs hT hc he₀), hle⟩
        · exact hle.elim
      | denote hreg hargs' hT hc hx hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨rs, t₀, s₀⟩
        · exact ⟨_, ub (.denoteUB hreg hargs hT hc he₀), TraceEnd.Allows.ub_prefix hle _⟩
        · obtain ⟨hrs, ht, hs₀⟩ := hle
          have hvs := HVector.toDVals_isRefinedBy hrs
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          obtain ⟨e₁, he₁, hle₁⟩ := ihn f _ _ os s₀ _ hf hops' (henv.zip_append _ hvs) hs₀ _ he
            (TraceEnd.NotStuck.of_after hne)
          exact ⟨_, src ((hle₁.after ht).notStuck fun _ _ h => h) (.denote hreg hargs hT hc he₀ hlen he₁),
            hle₁.after ht⟩
      | callUB hreg hargs' hT hc hg hen' hx =>
        obtain ⟨args, genv, e₀, hargs, hen, he₀, hle⟩ := callee hargs' hg hen' hx (TraceEnd.notStuck_error _ _)
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact ⟨_, ub (.callUB hreg hargs hT hc hg hen he₀), hle⟩
        · exact hle.elim
      | callExh hreg hargs' hT hc hg hen' hx =>
        obtain ⟨args, genv, e₀, hargs, hen, he₀, hle⟩ := callee hargs' hg hen' hx (TraceEnd.notStuck_ok _ _ _)
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨x, t₀, s₀⟩
        · exact ⟨_, ub (.callUB hreg hargs hT hc hg hen he₀), hle⟩
        · rcases x with _ | (_ | _) <;> obtain ⟨hx₀, ht, hs₀⟩ := hle
          · exact hx₀.elim
          · exact hx₀.elim
          · exact ⟨_, src (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT hc hg hen he₀),
              trivial, ht, hs₀⟩
      | callRet hreg hargs' hT hc hg hen' hx hty' hlen' he =>
        obtain ⟨args, genv, e₀, hargs, hen, he₀, hle⟩ := callee hargs' hg hen' hx (TraceEnd.notStuck_ok _ _ _)
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨x, t₀, s₀⟩
        · exact ⟨_, ub (.callUB hreg hargs hT hc hg hen he₀), TraceEnd.Allows.ub_prefix hle _⟩
        · rcases x with _ | (⟨vs, k⟩ | _) <;> obtain ⟨hx₀, ht, hs₀⟩ := hle
          · exact hx₀.elim
          · obtain ⟨hvs, rfl⟩ := hx₀
            have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
            have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
            obtain ⟨e₁, he₁, hle₁⟩ := ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) f _ _ os s₀ _
              hf hops' (henv.zip_append _ hvs) hs₀ _ he (TraceEnd.NotStuck.of_after hne)
            exact ⟨_, src ((hle₁.after ht).notStuck fun _ _ h => h)
              (.callRet hreg hargs hT hc hg hen he₀ hty hlen he₁), hle₁.after ht⟩
          · exact hx₀.elim

end Fir
