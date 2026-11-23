import Fir.Execution.TraceGuard
import Fir.Execution.TraceCallSource

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
recursion are included. An external-call rule may be monotone only where
two calls agree, so the two runs start from a pair of a guard
(`Fir.Execution.TraceGuard`), and the source takes, at each step, the step
that the guard picks: at each external call, one where the two calls
agree.

The proof is the one with memory (`Fir.Execution.MemoryRefineUp`), read in
the traced layer, by strong induction on the target's budget, for every
function at once and from every traced state:

* An op's operands are found in the source's environment too, refined, and
  it starts from a traced state that the target's refines. What it does in
  the target is allowed by what it does in the source: UB after acts that
  the target first shows, refined, which allows anything that shows them;
  otherwise results that the target's refine, or the same place to go,
  after a marked trace that the target's refines, in a traced state that the
  target's refines. The guard then gives such a step that ends in a pair of
  its own, and the induction covers the rest from there.
* A call of the same function in both enters it at the same op, from
  traced states with a frame entered, at the entry that the guard pairs;
  the induction covers the callee, and
  leaving a frame keeps refinement. A call of a black box is allowed by the
  black box's behaviours, which speak of the traced states the call starts
  and ends in. A call to an external declaration in the target is one in
  the source, which runs the same rule, monotone where the two calls agree,
  as they do at the call that the guard picks.
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

variable {agree : List (DVal d) → TraceState Mem unit → List (DVal d) → TraceState Mem unit → Prop}
  {G : TCfg d Mem unit → TCfg d Mem unit → Prop}

/-- Every return and UB of the target's traced run of ops is allowed by the
source's at some budget, comparing acts, from environments and traced
states of which the target's refine the source's, paired in a guard `G`,
when every call names the same function in both modules or a traced black
box, and every terminator and every op with no callee is monotone in the
traced layer, and every external-call rule where the calls agree, among the
ops of the source module's functions, of the function `f` that runs, and of
the ops `os` it runs. The source takes, at each step, a step that the guard
picks. -/
theorem Func.traceOps_tAllowed {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step A) (TraceState Mem unit) agree)
    (hcalls : TraceCallsRefined A Mem unit M M') (hG : TCfg.Guard A agree M M' G) (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (s s' : TraceState Mem unit),
      f.TraceOpsMonotone (Step A) (TraceState Mem unit) agree →
      TraceMonotoneOps (Step A) (TraceState Mem unit) os agree → env.IsRefinedBy env' → s ⊑ s' →
      G ⟨f, env, os, s⟩ ⟨f, env', os, s'⟩ →
      ∀ e', Func.traceOps (Step A) M' n f env' os s' e' →
        TAllowed (fun N => Func.traceOps (Step A) M N f env os s) e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os s s' hf hops henv hS hGc e' he'
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
    match n, os, hops, he', hGc with
    | 0, _, _, he', _ =>
      cases Func.traceOps_zero.1 he'
      exact hd.elim
    | n + 1, [], _, he', _ => exact absurd he' (Func.traceOps_nil hne)
    | n + 1, o :: os, hops, he', hGc =>
      have hmo := (hops o List.mem_cons_self).1
      have hext : TraceMonotoneOps (Step A) (TraceState Mem unit) [o] agree := fun o' h => by
        rw [List.mem_singleton.1 h]; exact hops o List.mem_cons_self
      have hpick := (hops o List.mem_cons_self).2.2
      have hops' : TraceMonotoneOps (Step A) (TraceState Mem unit) os agree :=
        fun o' h => hops o' (List.mem_cons_of_mem _ h)
      -- UB of the first op after a marked trace that the target's path first shows.
      have early : ∀ {r : String} {t₀ : List (Step A)},
          Func.TStepPath M 0 f env o os s (.error (r, t₀)) →
          List.IsRefinedPrefix t₀ (TraceEnd.trace e') →
          TAllowed (fun N => Func.traceOps (Step A) M N f env (o :: os) s) e' :=
        fun h hle => TAllowed.of_someUB ⟨1, _, _, hub h, Step.actsOf_isRefinedPrefix hle⟩
      -- The target's step of its frame, which the source follows by a step the guard picks.
      have go : ∀ {c₁' : TCfg d Mem unit} {t' : List (Step A)} {F' m : Nat} {e₁'}, m < n + 1 →
          TCfg.Next A M' ⟨f, env', o :: os, s'⟩ c₁' t' F' → c₁'.f = f →
          TraceMonotoneOps (Step A) (TraceState Mem unit) c₁'.os agree →
          Func.traceOps (Step A) M' m c₁'.f c₁'.env c₁'.os c₁'.s e₁' →
          (∃ c₁ t F, TCfg.Next A M ⟨f, env, o :: os, s⟩ c₁ t F ∧ c₁.Matched c₁' ∧
            Step.actsOf t ⊑ Step.actsOf t') →
          TAllowed (fun N => Func.traceOps (Step A) M N f env (o :: os) s) (e₁'.after t') := by
        intro c₁' t' F' m e₁' hm hn' hf₁ hops₁ he₁ hsrc
        obtain ⟨⟨f₂, env₂, os₂, s₂⟩, t₂, F₂, hn₂, hm₂, ht₂, hG₂⟩ := hG.next hGc hn' hsrc
        rcases c₁' with ⟨f₁, env₁', os₁, s₁'⟩
        obtain ⟨rfl, rfl, henv₂, hs₂⟩ := hm₂
        dsimp only at hf₁
        subst hf₁
        exact hn₂.tAllowed ht₂ (ih m hm _ _ _ _ _ _ hf hops₁ henv₂ hs₂ hG₂ _ he₁)
      -- The source's call, or its rule that picks the callee hitting UB.
      have src := fun {args args'} (hr : args.Forall₂ TyRefinement.IsRefinedBy args') {n₀ sym ts}
          {cargs' : HVector toType ts} {n' t₀' s₁'} (hT : isTerminator o.op = false)
          (hc : Func.TCallsAt M' o args' s' n₀ sym ts cargs' n' t₀' s₁') =>
        hc.source (M := M) (args := args) hr hS hcalls.2.2 fun hpc => (hpick hT hpc).1
      -- A call of a callee that both modules run: the source's call that the guard picks.
      have enter : ∀ {args args' : HVector toType (sig o.op)} {n₀ n' : Nat} {sym : Name}
          {ts : List d.Ty} {cargs : HVector toType ts} {cargs' : HVector toType ts}
          {t₀ t₀' : List (Step A)} {s₁ s₁' : TraceState Mem unit} {g₀ : Func d}
          {body : List (Operation d)} {genv' : Env d},
          env.operands (sig o.op) o.operands = .ok args →
          env'.operands (sig o.op) o.operands = .ok args' → isTerminator o.op = false →
          Func.TCallsAt M' o args' s' n₀ sym ts cargs' n' t₀' s₁' → M'.func? sym = some g₀ →
          g₀.enter cargs'.toDVals = .ok (body, genv') →
          Func.TCallsAt M o args s n₀ sym ts cargs n' t₀ s₁ →
          cargs.Forall₂ TyRefinement.IsRefinedBy cargs' → t₀ ⊑ t₀' → s₁ ⊑ s₁' →
          ∃ (cargs₂ : HVector toType ts) (t₀₂ : List (Step A)) (s₁₂ : TraceState Mem unit),
            Func.TCallsAt M o args s n₀ sym ts cargs₂ n' t₀₂ s₁₂ ∧
            cargs₂.Forall₂ TyRefinement.IsRefinedBy cargs' ∧ t₀₂ ⊑ t₀' ∧ s₁₂ ⊑ s₁' ∧
            (M'.func? sym = M.func? sym → ∀ genv, g₀.enter cargs₂.toDVals = .ok (body, genv) →
              G ⟨g₀, genv, body, { s₁₂ with mem := s₁₂.mem.enter }⟩
                ⟨g₀, genv', body, { s₁' with mem := s₁'.mem.enter }⟩) := by
        intro args args' n₀ n' sym ts cargs cargs' t₀ t₀' s₁ s₁' g₀ body genv' hargs hargs' hT hc hg'
          hen' hc₀ hcr ht₀ hs₁
        by_cases hsame : M'.func? sym = M.func? sym
        · obtain ⟨cargs₂, t₀₂, s₁₂, genv₂, hc₂, hr₂, ht₂, hs₂, hen₂, hG₂⟩ :=
            hG.enter hGc rfl rfl hargs hargs' hT hc (hsame ▸ hg') hg' hen'
              ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩
          refine ⟨cargs₂, t₀₂, s₁₂, hc₂, hr₂, ht₂, hs₂, fun _ genv hen => ?_⟩
          rw [hen₂] at hen
          cases hen
          exact hG₂
        · exact ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁, fun h => absurd h hsame⟩
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
          exact go (Nat.lt_succ_self n) (.goto hreg hargs' hT hos hx hj) rfl (hf.jump hj) he
            ⟨_, t₀, 1, .goto hreg hargs hT hos he₀ hj₁, ⟨rfl, rfl, henv₁, hs₀⟩,
              Step.actsOf_isRefinedBy ht⟩
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
          exact go (Nat.lt_succ_self n) (.denote hreg hargs' hT hc hx hlen') rfl hops' he
            ⟨_, t₀, 1, .denote hreg hargs hT hc he₀ hlen, ⟨rfl, rfl, henv.zip_append _ hvs, hs₀⟩,
              Step.actsOf_isRefinedBy ht⟩
      | callUB hreg hargs' hT hc hg' hen' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩ | ⟨hpc, r, t, hpu, htp⟩ := src hr hT hc
        case inr =>
          refine early (.pickUB hreg hargs hT hpc hpu) ?_
          rw [TraceEnd.trace_after]
          exact htp.append_right _
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁, hGe⟩ :=
          enter hargs hargs' hT hc hg' hen' hc₀ hcr ht₀ hs₁
        obtain ⟨g, p, hg, hen, ⟨N, r, mt, hN, hle⟩⟩ := hcalls.callee_allowed hmono hg' hcr hs₁
          (p' := (_, _)) hen' hGe
          (fun hgm hbm env env' h t t' ht hGt e' he' =>
            ih _ (Nat.lt_succ_of_le hc.le.1) _ env env' _ t t' hgm hbm h ht hGt e' he') hx
          trivial
        refine TAllowed.of_someUB ⟨_, r, t₀ ++ mt,
          hub (.callUB hreg hargs hT (hc₀.at N) hg hen hN), ?_⟩
        rw [TraceEnd.trace_after, Step.actsOf_append, Step.actsOf_append]
        exact hle.append_left (Step.actsOf_isRefinedBy ht₀)
      | callExh _ _ _ _ _ _ _ => exact hd.elim
      | pickExh _ _ _ _ _ _ => exact hd.elim
      | pickUB hreg hargs' hT hpc hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hpick hT hpc).1 _ _ (hcalls.2.2 _ _) args _ hr s s' hS _ hx
        rcases e₀ with ⟨r₀, t₀⟩ | ⟨_, _, _⟩
        · exact early (.pickUB hreg hargs hT hpc he₀) hle
        · exact hle.elim
      | @callRet _ _ _ _ n' _ _ _ _ _ _ _ _ _ _ hreg hargs' hT hc hg' hen' hx hty' hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩ | ⟨hpc, r, t, hpu, htp⟩ := src hr hT hc
        case inr =>
          refine early (.pickUB hreg hargs hT hpc hpu) ?_
          rw [TraceEnd.trace_after]
          exact htp.append_right _
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁, hGe⟩ :=
          enter hargs hargs' hT hc hg' hen' hc₀ hcr ht₀ hs₁
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hcr hs₁ (p' := (_, _)) hen'
          hGe (fun hgm hbm env env' h t t' ht hGt e' he' =>
            ih _ (Nat.lt_succ_of_le hc.le.1) _ env env' _ t t' hgm hbm h ht hGt e' he') hx
          trivial
        rcases hm with ⟨N, r, mt, hN, hle⟩ | ⟨N₁, vs, k₁, tc, s₂, hx₁, hvs, htc, hs₂⟩
        · refine TAllowed.of_someUB ⟨_, r, t₀ ++ mt,
            hub (.callUB hreg hargs hT (hc₀.at N) hg hen hN), ?_⟩
          rw [TraceEnd.trace_after, TraceEnd.trace_after, Step.actsOf_append, Step.actsOf_append,
            Step.actsOf_append]
          exact (hle.append_right _).append_left (Step.actsOf_isRefinedBy ht₀)
        have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
        have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
        rw [TraceEnd.after_after]
        exact go (Nat.lt_succ_of_le (Nat.le_trans (Nat.min_le_right _ _) hc.le.1))
          (.ret hreg hargs' hT (hc.at 0) hg' hen' hx hty' hlen') rfl hops' he
          ⟨_, t₀ ++ tc, _, .ret hreg hargs hT (hc₀.at 0) hg hen hx₁ hty hlen,
            ⟨rfl, rfl, henv.zip_append _ hvs, hs₂⟩, by
              rw [Step.actsOf_append, Step.actsOf_append]
              exact List.IsRefinedBy.append (Step.actsOf_isRefinedBy ht₀) htc⟩
      | extUB hreg hargs' hT hc hg' hd' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨hg, hd⟩ := hcalls.ext hg' hd'
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩ | ⟨hpc, r, t, hpu, htp⟩ := src hr hT hc
        case inr =>
          refine early (.pickUB hreg hargs hT hpc hpu) ?_
          rw [TraceEnd.trace_after]
          exact htp.append_right _
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁, hag⟩ :=
          hG.ext hGc rfl rfl hargs hargs' hT hc hg' ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩
        obtain ⟨e₀, he₀, hle⟩ := hc₀.extMonotone hT hext cargs _ hcr s₁ _ hs₁ hag _ hx
        rcases e₀ with ⟨r₀, t'⟩ | ⟨_, _, _⟩
        · refine TAllowed.of_someUB ⟨_, r₀, t₀ ++ t',
            hub (.extUB hreg hargs hT (hc₀.at 0) hg hd he₀), ?_⟩
          rw [TraceEnd.trace_after, Step.actsOf_append, Step.actsOf_append]
          exact (Step.actsOf_isRefinedPrefix hle).append_left (Step.actsOf_isRefinedBy ht₀)
        · exact hle.elim
      | @ext _ _ _ _ n' _ _ _ _ _ _ hreg hargs' hT hc hg' hd' hx hty' hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨hg, hd⟩ := hcalls.ext hg' hd'
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩ | ⟨hpc, r, t, hpu, htp⟩ := src hr hT hc
        case inr =>
          refine early (.pickUB hreg hargs hT hpc hpu) ?_
          rw [TraceEnd.trace_after]
          exact htp.append_right _
        obtain ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁, hag⟩ :=
          hG.ext hGc rfl rfl hargs hargs' hT hc hg' ⟨cargs, t₀, s₁, hc₀, hcr, ht₀, hs₁⟩
        obtain ⟨e₀, he₀, hle⟩ := hc₀.extMonotone hT hext cargs _ hcr s₁ _ hs₁ hag _ hx
        rcases e₀ with ⟨r₀, t'⟩ | ⟨vs, t', s₀⟩
        · refine TAllowed.of_someUB ⟨_, r₀, t₀ ++ t',
            hub (.extUB hreg hargs hT (hc₀.at 0) hg hd he₀), ?_⟩
          rw [TraceEnd.trace_after, TraceEnd.trace_after, Step.actsOf_append, Step.actsOf_append,
            Step.actsOf_append]
          exact ((Step.actsOf_isRefinedPrefix hle).append_right _).append_left
            (Step.actsOf_isRefinedBy ht₀)
        · obtain ⟨hvs, ht, hs₀⟩ := hle
          have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          rw [TraceEnd.after_after]
          exact go (Nat.lt_succ_of_le hc.le.1) (.ext hreg hargs' hT (hc.at 0) hg' hd' hx hty' hlen')
            rfl hops' he
            ⟨_, t₀ ++ t', _, .ext hreg hargs hT (hc₀.at 0) hg hd he₀ hty hlen,
              ⟨rfl, rfl, henv.zip_append _ hvs, hs₀⟩, by
                rw [Step.actsOf_append, Step.actsOf_append]
                exact List.IsRefinedBy.append (Step.actsOf_isRefinedBy ht₀) (Step.actsOf_isRefinedBy ht)⟩

end Fir
