import Fir.Execution.TraceBlackBox

/-!
# Every return and UB of the target, allowed, call by call

Let every call name the same function in both modules or a traced black
box, and the source declare each symbol that the target declares. Let
every op that runs by
its own rule, a terminator or an op with no callee, be monotone in the
traced layer of marked traces, and the external-call rule at each other
call, among the ops of the source module's functions and of the function
that runs. Then every
return and every UB of the target's traced run of ops, from an environment
and a traced state that refine the source's, is allowed by the source's run
of the same ops at some budget, comparing acts. Calls, black boxes and
recursion are included.

The proof is the one with memory (`Fir.Execution.MemoryRefineUp`), read in
the traced layer, by strong induction on the target's budget, for every
function at once and from every traced state:

* An op's operands are found in the source's environment too, refined, and
  it starts from a traced state that the target's refines. What it does in
  the target is allowed by what it does in the source: UB after acts that
  the target first shows, refined, which allows anything that shows them;
  otherwise results that the target's refine, or the same place to go,
  after a marked trace that the target's refines, in a traced state that the
  target's refines. The induction covers the rest.
* A call of the same function in both enters it at the same op, from
  traced states with a frame entered; the induction covers the callee, and
  leaving a frame keeps refinement. A call of a black box is allowed by the
  black box's behaviours, which speak of the traced states the call starts
  and ends in. A call to an external declaration in the target is one in
  the source, which runs the same monotone rule.
* When the source's callee returns at one budget, and the rest of the
  source's run is allowed at another, the source's run is allowed at their
  sum plus one: with more fuel the callee returns with more steps left
  (`Fir.Execution.TraceAhead`), and the rest ends as it did.
-/

namespace Fir

open Memory

variable {A : Type} [HRefinement A A] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] [TyRefinement d.Ty]

/-- A return or UB of a call's callee in the target, in its frame, is
allowed by the source's callee in its frame: the same function, by the
induction `ih`, or a black box. The induction is asked only of a function
of the source module, whose ops are monotone, from the ops of its entry
block. -/
theorem TraceCallsRefined.callee_allowed {M M' : Module d}
    (hc : TraceCallsRefined A Mem unit M M')
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step A) (TraceState Mem unit))
    {sym : Name} {g₀ : Func d} (hg' : M'.func? sym = some g₀) {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {s s' : TraceState Mem unit} (hs : s ⊑ s') {p' : List (Operation d) × Env d}
    (hen' : g₀.enter args'.toDVals = .ok p') {n : Nat}
    (ih : g₀.TraceOpsMonotone (Step A) (TraceState Mem unit) →
      TraceMonotoneOps (Step A) (TraceState Mem unit) p'.1 → ∀ (env env' : Env d),
      env.IsRefinedBy env' → ∀ (t t' : TraceState Mem unit), t ⊑ t' →
      ∀ e', Func.traceOps (Step A) M' n g₀ env' p'.1 t' e' →
        TAllowed (fun N => Func.traceOps (Step A) M N g₀ env p'.1 t) e')
    {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : Func.traceCall (Step A) M' n g₀ p'.2 p'.1 s' e') (hd : e'.Done) :
    ∃ g p, M.func? sym = some g ∧ g.enter args.toDVals = .ok p ∧
      TAllowed (fun N => Func.traceCall (Step A) M N g p.2 p.1 s) e' := by
  rcases hc.1 sym with hsame | ⟨g, g', hg, hg'', bb⟩
  · obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    have hg : M.func? sym = some g₀ := hsame ▸ hg'
    have hf := hmono g₀ (List.mem_of_find?_eq_some hg)
    exact ⟨g₀, (p'.1, genv), hg, hen, Func.traceCall_tAllowed
      (fun e₀ he₀ => ih hf (hf.enter hen') genv p'.2 hgenv _ _ (TraceState.IsRefinedBy.enter hs) e₀ he₀) he'⟩
  · rw [hg''] at hg'
    cases hg'
    obtain ⟨p, hen, hm⟩ := bb.allowed hr hs hen' he' hd
    exact ⟨g, p, hg, hen, hm⟩

/-- Every return and UB of the target's traced run of ops is allowed by the
source's at some budget, comparing acts, from environments and traced
states of which the target's refine the source's, when every call names the
same function in both modules or a traced black box, and every terminator
and every op with no callee is monotone in the traced layer, among the ops
of the source module's functions, of the function `f` that runs, and of the
ops `os` it runs. -/
theorem Func.traceOps_tAllowed {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step A) (TraceState Mem unit))
    (hcalls : TraceCallsRefined A Mem unit M M') (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (s s' : TraceState Mem unit),
      f.TraceOpsMonotone (Step A) (TraceState Mem unit) →
      TraceMonotoneOps (Step A) (TraceState Mem unit) os → env.IsRefinedBy env' → s ⊑ s' →
      ∀ e', Func.traceOps (Step A) M' n f env' os s' e' →
        TAllowed (fun N => Func.traceOps (Step A) M N f env os s) e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os s s' hf hops henv hS e' he'
    classical
    by_cases hd : e'.Done
    case neg =>
      rcases e' with _ | ⟨_ | (_ | _), _, _⟩
      all_goals first | trivial | exact (hd trivial).elim
    have hne := hd.notStuck
    have hub : ∀ {N : Nat} {r : String} {t : List (Step A)} {o : Operation d}
        {os : List (Operation d)}, Func.TStepPath M N f env o os s (.error (r, t)) →
        Func.traceOps (Step A) M (N + 1) f env (o :: os) s (.error (r, t)) :=
      fun h => (Func.tStepPath_iff (TraceEnd.notStuck_error _ _)).2 h
    match n, os, hops, he' with
    | 0, _, _, he' =>
      cases Func.traceOps_zero.1 he'
      exact hd.elim
    | n + 1, [], _, he' => exact absurd he' (Func.traceOps_nil hne)
    | n + 1, o :: os, hops, he' =>
      have ihn := ih n (Nat.lt_succ_self n)
      have hmo := (hops o List.mem_cons_self).1
      have hext := (hops o List.mem_cons_self).2
      have hops' : TraceMonotoneOps (Step A) (TraceState Mem unit) os :=
        fun o' h => hops o' (List.mem_cons_of_mem _ h)
      -- UB of the first op after a marked trace that the target's path first shows.
      have early : ∀ {r : String} {t₀ : List (Step A)},
          Func.TStepPath M 0 f env o os s (.error (r, t₀)) →
          List.IsRefinedPrefix t₀ (TraceEnd.trace e') →
          TAllowed (fun N => Func.traceOps (Step A) M N f env (o :: os) s) e' :=
        fun h hle => TAllowed.of_someUB ⟨1, _, _, hub h, Step.actsOf_isRefinedPrefix hle⟩
      have step : ∀ {c : Nat → Paths (TraceEnd (Step A) (TraceState Mem unit)
            (Except Stuck (Result (List (DVal d) × Nat))))} {t₀ t' : List (Step A)} {e₁'},
          t₀ ⊑ t' → (∀ N x, TraceEnd.NotStuck x → c N x → Func.TStepPath M N f env o os s (x.after t₀)) →
          TAllowed c e₁' →
          TAllowed (fun N => Func.traceOps (Step A) M N f env (o :: os) s) (e₁'.after t') :=
        fun ht hcp => TAllowed.of_step (k := 0) (N₀ := 0) (Step.actsOf_isRefinedBy ht)
          fun N x hx h => by
            rw [Nat.zero_add, TraceEnd.addLeft_zero]
            exact (Func.tStepPath_iff hx.notStuck.after).2 (hcp N x hx.notStuck h)
      cases (Func.tStepPath_iff hne).1 he' with
      | exitUB hreg hargs' hT hos hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact early (.exitUB hreg hargs hT hos he₀) hle
        · exact hle.elim
      | ret hreg hargs' hT hos hx hs =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨x, t₀, s₀⟩
        · exact early (.exitUB hreg hargs hT hos he₀) hle
        · obtain ⟨rfl, ht, hs₀⟩ := hle
          exact .inr ⟨1, _, 0, t₀, s₀, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
            (.ret hreg hargs hT hos he₀ hs), HVector.toDVals_isRefinedBy hr,
            Step.actsOf_isRefinedBy ht, hs₀⟩
      | goto hreg hargs' hT hos hx hj he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨x, t₀, s₀⟩
        · refine early (.exitUB hreg hargs hT hos he₀) ?_
          rw [TraceEnd.trace_after]
          exact hle.append_right _
        · obtain ⟨rfl, ht, hs₀⟩ := hle
          obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
          exact step ht (fun N x _ h => .goto hreg hargs hT hos he₀ hj₁ h)
            (ihn _ _ _ _ _ _ hf (hf.jump hj₁) henv₁ hs₀ _ he)
      | denoteUB hreg hargs' hT hc hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact early (.denoteUB hreg hargs hT hc he₀) hle
        · exact hle.elim
      | denote hreg hargs' hT hc hx hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨rs, t₀, s₀⟩
        · refine early (.denoteUB hreg hargs hT hc he₀) ?_
          rw [TraceEnd.trace_after]
          exact hle.append_right _
        · obtain ⟨hrs, ht, hs₀⟩ := hle
          have hvs := HVector.toDVals_isRefinedBy hrs
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          exact step ht (fun N x _ h => .denote hreg hargs hT hc he₀ hlen h)
            (ihn _ _ _ _ _ _ hf hops' (henv.zip_append _ hvs) hs₀ _ he)
      | callUB hreg hargs' hT hc hg' hen' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, ⟨N, r, mt, hN, hle⟩⟩ := hcalls.callee_allowed hmono hg' hr hS
          (p' := (_, _)) hen'
          (fun hgm hbm env env' h t t' ht e' he' => ihn _ env env' _ t t' hgm hbm h ht e' he') hx
          trivial
        exact TAllowed.of_someUB ⟨N + 1, r, mt, hub (.callUB hreg hargs hT hc hg hen hN), hle⟩
      | callExh _ _ _ _ _ _ _ => exact hd.elim
      | callRet hreg hargs' hT hc hg' hen' hx hty' hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hr hS (p' := (_, _)) hen'
          (fun hgm hbm env env' h t t' ht e' he' => ihn _ env env' _ t t' hgm hbm h ht e' he') hx
          trivial
        rcases hm with ⟨N, r, mt, hN, hle⟩ | ⟨N₁, vs, k₁, tc, s₁, hx₁, hvs, htc, hs₁⟩
        · refine TAllowed.of_someUB ⟨N + 1, r, mt, hub (.callUB hreg hargs hT hc hg hen hN), ?_⟩
          rw [TraceEnd.trace_after, Step.actsOf_append]
          exact hle.append_right _
        have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
        have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
        have hm := ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _ _ _ _ hf hops'
          (henv.zip_append _ hvs) hs₁ _ he
        refine TAllowed.of_step (k := min k₁ N₁) (N₀ := N₁) htc (fun N₂ x hx h => ?_) hm
        have hcall := Func.traceCall_up N₂ N₁ hx₁ trivial
        have hrest := Func.traceOps_up (min k₁ N₁) N₂ _ _ _ _ _ h hx
        have hmin : min (k₁ + N₂) (N₁ + N₂) = N₂ + min k₁ N₁ := by
          rw [Nat.add_min_add_right, Nat.add_comm]
        exact (Func.tStepPath_iff (hx.addLeft _).notStuck.after).2
          (.callRet hreg hargs hT hc hg hen hcall hty hlen (hmin ▸ hrest))
      | extUB hreg hargs' hT hc hg' hd' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨hg, hd⟩ := hcalls.ext hg' hd'
        obtain ⟨e₀, he₀, hle⟩ := hext hT _ hc args _ hr s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact early (.extUB hreg hargs hT hc hg hd he₀) hle
        · exact hle.elim
      | ext hreg hargs' hT hc hg' hd' hx hty' hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨hg, hd⟩ := hcalls.ext hg' hd'
        obtain ⟨e₀, he₀, hle⟩ := hext hT _ hc args _ hr s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨vs, t₀, s₀⟩
        · refine early (.extUB hreg hargs hT hc hg hd he₀) ?_
          rw [TraceEnd.trace_after]
          exact hle.append_right _
        · obtain ⟨hvs, ht, hs₀⟩ := hle
          have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          exact step ht (fun N x _ h => .ext hreg hargs hT hc hg hd he₀ hty hlen h)
            (ihn _ _ _ _ _ _ hf hops' (henv.zip_append _ hvs) hs₀ _ he)

end Fir
