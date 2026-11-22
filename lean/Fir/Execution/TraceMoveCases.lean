import Fir.Execution.TraceMoves
import Fir.Execution.TraceFiniteRuns

/-!
# The first move of a path

Each path of a configuration's run that runs out of fuel at a budget of at
least one goes on by a first move (`TCfg.exh_succ`):

* an op that runs by its own rule, or a call of an external declaration,
  with one of its outcomes, or a call that enters its callee whose path
  runs out of fuel: a move of one step of fuel,
  after which the rest runs out of fuel at one step fewer;
* or a call whose callee returns: the configuration's first op calls a
  function of the module (`TCfg.Calls`), and the path is the callee's return,
  then the rest, which runs out of fuel at the steps the callee leaves
  (`TCfg.exh_succ_of_calls`).

When every op that runs by its own rule, and every external call, has
finitely many outcomes, given the world's answers, a configuration has
finitely many moves of one step of fuel whose acts agree with an answer
stream (`TCfg.moves_one_finite`): the outcomes of its first op or of its
external call, and the one callee it may enter.
-/

namespace Fir

open Memory

variable {A : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {M : Module d}

/-- The first op of the configuration calls the function `g` of the module
`M`, which it enters at the ops `body` with the environment `genv`. -/
def TCfg.Calls (M : Module d) (c : TCfg d Mem unit) (g : Func d) (body : List (Operation d))
    (genv : Env d) : Prop :=
  ∃ o os, c.os = o :: os ∧ o.ownsCoreRegion = false ∧ isTerminator o.op = false ∧
    ∃ (args : HVector toType (sig o.op)), ∃ sym, c.env.operands (sig o.op) o.operands = .ok args ∧
      callee? o.op = some sym ∧ M.func? sym = some g ∧ g.enter args.toDVals = .ok (body, genv)

/-- The configuration after a call of its first op returns the values `vs`
in the traced state `s₁`: the results bound, the rest of its ops to run. -/
def TCfg.after (c : TCfg d Mem unit) (vs : List (DVal d)) (s₁ : TraceState Mem unit) :
    TCfg d Mem unit :=
  match c.os with
  | o :: os => ⟨c.f, (o.results.map (·.1)).zip vs ++ c.env, os, s₁⟩
  | [] => c

variable [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))]

/-- A configuration whose first op calls a function enters it by a move. -/
theorem TCfg.Calls.enter {c : TCfg d Mem unit} {g : Func d} {body : List (Operation d)}
    {genv : Env d} (h : c.Calls M g body genv) :
    TCfg.Move A M c ⟨g, genv, body, { c.s with mem := c.s.mem.enter }⟩ [] 1 := by
  obtain ⟨o, os, hos, hreg, hT, args, sym, hargs, hc, hg, hen⟩ := h
  rcases c with ⟨f, env, os', s⟩
  dsimp only at hos
  subst hos
  exact .enter hreg hargs hT hc hg hen

/-- Each path of a configuration's run that runs out of fuel at a budget of at
least one goes on by a move of one step of fuel, then runs out of fuel at one
step fewer; or the configuration's first op calls a function of the module. -/
theorem TCfg.exh_succ {c : TCfg d Mem unit} {n : Nat} {mt : List (Step A)}
    (h : c.exh A M (n + 1) mt) :
    (∃ c₁ t mt₁, TCfg.Move A M c c₁ t 1 ∧ c₁.exh A M n mt₁ ∧ mt = t ++ mt₁) ∨
      ∃ g body genv, c.Calls M g body genv := by
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
        (Except Stuck (Result (List (DVal d) × Nat)))} {t : List (Step A)},
        .ok (.ok .fuelExhausted, mt, s₁) = TraceEnd.after t e →
        ∃ mt₁, e = .ok (.ok .fuelExhausted, mt₁, s₁) ∧ mt = t ++ mt₁ := by
      intro e t he
      rcases e with ⟨_, _⟩ | ⟨y, t', s'⟩
      · cases he
      · simp only [TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨t', rfl, rfl⟩
    cases hpath with
    | exitUB => cases hE
    | ret => cases hE
    | denoteUB => cases hE
    | callUB => cases hE
    | goto hreg hargs hT hos hx hj hr =>
      obtain ⟨mt₁, rfl, rfl⟩ := after hE
      exact .inl ⟨_, _, mt₁, .goto hreg hargs hT hos hx hj, ⟨s₁, hr⟩, rfl⟩
    | denote hreg hargs hT hc hx hlen hr =>
      obtain ⟨mt₁, rfl, rfl⟩ := after hE
      exact .inl ⟨_, _, mt₁, .denote hreg hargs hT hc hx hlen, ⟨s₁, hr⟩, rfl⟩
    | extUB => cases hE
    | ext hreg hargs hT hc hg hd hx hty hlen hr =>
      obtain ⟨mt₁, rfl, rfl⟩ := after hE
      exact .inl ⟨_, _, mt₁, .ext hreg hargs hT hc hg hd hx hty hlen, ⟨s₁, hr⟩, rfl⟩
    | callExh hreg hargs hT hc hg hen hx =>
      cases hE
      obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 hx
      rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
      · cases he₁
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
      obtain ⟨rfl, rfl, -⟩ := he₁
      exact .inl ⟨_, [], mt, .enter hreg hargs hT hc hg hen, ⟨s₂, h₁⟩, rfl⟩
    | callRet hreg hargs hT hc hg hen =>
      exact .inr ⟨_, _, _, o, os, rfl, hreg, hT, _, _, hargs, hc, hg, hen⟩

/-- When the configuration's first op calls a function, each path of its run
that runs out of fuel at a budget of at least one is a path of the callee that
runs out of fuel at one step fewer, from the traced state with a frame
entered; or the callee returns, after which the rest runs out of fuel at the
steps the callee leaves, and the configuration goes on by the move of that
return at every budget at which the callee returns the same. -/
theorem TCfg.exh_succ_of_calls {c : TCfg d Mem unit} {g : Func d} {body : List (Operation d)}
    {genv : Env d} (hcall : c.Calls M g body genv) {n : Nat} {mt : List (Step A)}
    (h : c.exh A M (n + 1) mt) :
    TCfg.exh A M ⟨g, genv, body, { c.s with mem := c.s.mem.enter }⟩ n mt ∨
      ∃ vs k t s₁ mt₁,
        Func.traceCall (Step A) M n g genv body c.s (.ok (.ok (.ret (vs, k)), t, s₁)) ∧
        (∀ U k', Func.traceCall (Step A) M U g genv body c.s (.ok (.ok (.ret (vs, k')), t, s₁)) →
          TCfg.Move A M c (c.after vs s₁) t (U + 1)) ∧
        (c.after vs s₁).exh A M (min k n) mt₁ ∧ mt = t ++ mt₁ := by
  obtain ⟨o, os, hos, hreg, hT, args, sym, hargs, hc, hg, hen⟩ := hcall
  rcases c with ⟨f, env, os', s⟩
  dsimp only at hos hargs ⊢
  subst hos
  obtain ⟨s₁, h⟩ := h
  have hpath := (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).1 h
  generalize hE : (Except.ok (Except.ok Result.fuelExhausted, mt, s₁) :
    TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) = E
    at hpath
  cases hpath with
  | exitUB => cases hE
  | ret => cases hE
  | denoteUB => cases hE
  | callUB => cases hE
  | goto _ _ hT' => rw [hT] at hT'; cases hT'
  | denote _ _ _ hc' => rw [hc] at hc'; cases hc'
  | extUB => cases hE
  | ext _ _ _ hc' hg' =>
    rw [hc] at hc'
    cases hc'
    rw [hg] at hg'
    cases hg'
  | callExh _ hargs' _ hc' hg' hen' hx =>
    cases hE
    rw [hargs] at hargs'
    cases hargs'
    rw [hc] at hc'
    cases hc'
    rw [hg] at hg'
    cases hg'
    rw [hen] at hen'
    cases hen'
    obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 hx
    rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
    · cases he₁
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
    obtain ⟨rfl, rfl, -⟩ := he₁
    exact .inl ⟨s₂, h₁⟩
  | @callRet args' sym' g' body' genv' vs k t s₂ e _ hargs' _ hc' hg' hen' hx hty hlen hr =>
    rw [hargs] at hargs'
    cases hargs'
    rw [hc] at hc'
    cases hc'
    rw [hg] at hg'
    cases hg'
    rw [hen] at hen'
    cases hen'
    rcases e with ⟨_, _⟩ | ⟨y, t', s'⟩
    · cases hE
    simp only [TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at hE
    obtain ⟨rfl, rfl, rfl⟩ := hE
    exact .inr ⟨vs, k, t, s₂, t', hx, fun U k' hU => .ret hreg hargs hT hc hg hen hU hty hlen,
      ⟨_, hr⟩, rfl⟩

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

/-- When every op that runs by its own rule has finitely many outcomes, given
the world's answers, a configuration has finitely many moves of one step of
fuel whose acts agree with an answer stream: the outcomes of its first op,
each with the configuration it goes on to, and the one callee it may
enter. -/
theorem TCfg.moves_one_finite (hfin : OpsStepFinite d E Ans (TraceState Mem unit))
    (c : TCfg d Mem unit) (ans : Nat → Option Ans) :
    ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))), ∀ c₁ t,
      TCfg.Move (Act E Ans) M c c₁ t 1 → Act.Agrees ans (Step.actsOf t) → (c₁, t) ∈ L := by
  classical
  rcases c with ⟨f, env, os, s⟩
  cases os with
  | nil => exact ⟨[], fun c₁ t h => by cases h⟩
  | cons o os =>
    cases hargs : env.operands (sig o.op) o.operands with
    | error _ =>
      refine ⟨[], fun c₁ t h _ => ?_⟩
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
      have Lc : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          ∀ sym (g : Func d) body genv, callee? o.op = some sym → M.func? sym = some g →
            g.enter args.toDVals = .ok (body, genv) →
            ((⟨g, genv, body, { s with mem := s.mem.enter }⟩ : TCfg d Mem unit), []) ∈ L := by
        by_cases hx : ∃ sym, ∃ (g : Func d), ∃ body genv, callee? o.op = some sym ∧
            M.func? sym = some g ∧ g.enter args.toDVals = .ok (body, genv)
        · obtain ⟨sym, g, body, genv, hc, hg, hen⟩ := hx
          refine ⟨[(⟨g, genv, body, { s with mem := s.mem.enter }⟩, [])],
            fun sym' g' body' genv' hc' hg' hen' => ?_⟩
          rw [hc] at hc'
          cases hc'
          rw [hg] at hg'
          cases hg'
          rw [hen] at hen'
          cases hen'
          exact List.mem_singleton_self _
        · exact ⟨[], fun sym g body genv hc hg hen => absurd ⟨sym, g, body, genv, hc, hg, hen⟩ hx⟩
      have Lx : ∃ L : List (TCfg d Mem unit × List (Step (Act E Ans))),
          ∀ sym (vs : List (DVal d)) t s₁, callee? o.op = some sym →
            DialectExtCall.extCall (m := TraceM (Step (Act E Ans)) (TraceState Mem unit)) sym
              args.toDVals (returnTypes o.op) s (.ok (vs, t, s₁)) →
            Act.Agrees ans (Step.actsOf t) →
            (⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₁⟩, t) ∈ L := by
        cases hc : callee? o.op with
        | none => exact ⟨[], fun _ _ _ _ h => by cases h⟩
        | some sym =>
          obtain ⟨L₀, hL₀⟩ := (hfin.2 sym args.toDVals (returnTypes o.op)) s ans
          refine ⟨L₀.map fun p => (⟨f, (o.results.map (·.1)).zip p.1 ++ env, os, p.2.2⟩, p.2.1),
            fun sym' vs t s₁ hc' hx hag => ?_⟩
          obtain rfl := Option.some.inj hc'
          exact List.mem_map.2 ⟨_, hL₀ _ _ _ hx hag, rfl⟩
      obtain ⟨Ld, hLd⟩ := Ld
      obtain ⟨Le, hLe⟩ := Le
      obtain ⟨Lc, hLc⟩ := Lc
      obtain ⟨Lx, hLx⟩ := Lx
      refine ⟨Lx ++ (Ld ++ Le ++ Lc), fun c₁ t h hag => ?_⟩
      cases h with
      | denote _ hargs' hT hc hx =>
        rw [hargs] at hargs'
        cases hargs'
        exact List.mem_append_right _
          (List.mem_append_left _ (List.mem_append_left _ (hLd hT hc _ _ _ hx hag)))
      | ext _ hargs' _ hc _ _ hx =>
        rw [hargs] at hargs'
        cases hargs'
        exact List.mem_append_left _ (hLx _ _ _ _ hc hx hag)
      | goto _ hargs' hT _ hx hj =>
        rw [hargs] at hargs'
        cases hargs'
        exact List.mem_append_right _
          (List.mem_append_left _ (List.mem_append_right _ (hLe hT _ _ _ _ _ hx hj hag)))
      | enter _ hargs' _ hc hg hen =>
        rw [hargs] at hargs'
        cases hargs'
        exact List.mem_append_right _ (List.mem_append_right _ (hLc _ _ _ _ hc hg hen))
      | ret _ _ _ _ _ _ hx =>
        obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 hx
        cases Func.traceOps_zero.1 h₁
        cases he₁

end Fir
