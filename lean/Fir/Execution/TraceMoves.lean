import Fir.Execution.TraceBranch
import Fir.Execution.TraceAhead
import Fir.Execution.TraceCallPace

/-!
# Moves of a traced run of ops

A run of ops, in the traced layer of marked traces, is fixed by its
_configuration_: the function that runs, its environment, the ops still to
run and the traced state (`TCfg`). Its paths that run out of fuel at each
budget, with their marked traces, and its paths that hit UB, are what the
proofs of divergence follow (`TCfg.exh`, `TCfg.ub`).

A configuration goes on to another by a _move_ (`TCfg.Move`):

* an op that runs by its own rule, a terminator that jumps among them, with
  one of its outcomes: its marked trace, of one step, and one step of fuel;
* a call of an external declaration, with one of the external-call rule's
  outcomes: its marked trace, of one step, and one step of fuel;
* a call that enters its callee: no marked trace of its own, and one step of
  fuel;
* a call whose callee returns at the budget `U`: the callee's marked trace,
  and `U + 1` steps of fuel.

A call whose callee its rule picks (#235) makes the same three moves after
the rule: their marked traces start with the rule's, of one step, and they
take one more step of fuel, the rule's (`δ`, the steps a call takes before
its callee's, `Func.TCallsAt`). With only one step of fuel, the rule runs
out of fuel within the move.

Each move is a move of the runs' paths that run out of fuel (`TCfg.Move.tStep`,
`Fir.Execution.TraceBranch`). With fuel enough, the configuration goes on
after the move's marked trace by every path of the next one; below the
move's fuel it runs out of fuel within the move. For a callee that returns,
more fuel lets it return with more steps left (`Func.traceCall_up`), and less
cuts it (`Func.traceOps_cut`), in the module whose chains of calls are
bounded. UB of the next configuration is UB of the configuration, after the
move's marked trace (`TCfg.Move.ub`). Only a move that enters a callee that
its op names shows no step, and it goes one call along the chain of calls of
the ops (`TCfg.Move.callHead`).
-/

namespace Fir

open Memory

/-- A configuration of a traced run of ops: the function `f` that runs, its
environment, the ops `os` still to run and the traced state. -/
structure TCfg (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (Mem : Type) (unit : Mem → Nat) where
  f : Func d
  env : Env d
  os : List (Operation d)
  s : TraceState Mem unit

variable {A : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M : Module d}

variable (A) in
/-- The marked traces of the paths of a configuration's run in the module `M`
that run out of fuel at each budget. -/
def TCfg.exh (M : Module d) (c : TCfg d Mem unit) (n : Nat) (mt : List (Step A)) : Prop :=
  ∃ s₁, Func.traceOps (Step A) M n c.f c.env c.os c.s (.ok (.ok .fuelExhausted, mt, s₁))

variable (A) in
/-- A configuration's run in the module `M` hits UB at the budget `n`, for the
reason `r`, after the marked trace `mt`. -/
def TCfg.ub (M : Module d) (c : TCfg d Mem unit) (n : Nat) (r : String) (mt : List (Step A)) : Prop :=
  Func.traceOps (Step A) M n c.f c.env c.os c.s (.error (r, mt))

variable (A) in
/-- A move from a configuration to the next in the module `M`, after the marked
trace `t` and with `F` steps of fuel: an op that runs by its own rule, with one
of its outcomes; a call that enters its callee; or a call whose callee returns
at the budget `U`. -/
inductive TCfg.Move (M : Module d) : TCfg d Mem unit → TCfg d Mem unit → List (Step A) → Nat → Prop
  | denote {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)}
      {rs : HVector toType (returnTypes o.op)} {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := TraceM (Step A) (TraceState Mem unit)) o.op args s (.ok (rs, t, s₁)) →
      (o.results.map (·.1)).length = rs.toDVals.length →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip rs.toDVals ++ env, os, s₁⟩ t 1
  | ext {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ s₂ : TraceState Mem unit} {args : HVector toType (sig o.op)} {δ : Nat} {sym : Name}
      {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)} {vs : List (DVal d)}
      {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ →
      M.func? sym = none → M.declares sym ts (returnTypes o.op) = true →
      DialectExtCall.extCall (m := TraceM (Step A) (TraceState Mem unit)) sym cargs.toDVals
        (returnTypes o.op) s₁ (.ok (vs, t, s₂)) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ (t₀ ++ t)
        (δ + 1)
  | goto {f : Func d} {env env₁ : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)} {i : Nat} {t : List (Step A)}
      {b : Block d} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM (Step A) (TraceState Mem unit)) o.op args s (.ok (.goto i, t, s₁)) →
      f.jump env o.succs i = .ok (b, env₁) →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨f, env₁, b.body, s₁⟩ t 1
  | enter {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)} {δ : Nat} {sym : Name}
      {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)} {g : Func d}
      {body : List (Operation d)} {genv : Env d} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ →
      M.func? sym = some g → g.enter cargs.toDVals = .ok (body, genv) →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨g, genv, body, { s₁ with mem := s₁.mem.enter }⟩ t₀ (δ + 1)
  | ret {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ s₂ : TraceState Mem unit} {args : HVector toType (sig o.op)} {δ : Nat} {sym : Name}
      {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)} {g : Func d}
      {body : List (Operation d)} {genv : Env d} {U k : Nat} {vs : List (DVal d)}
      {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ →
      M.func? sym = some g → g.enter cargs.toDVals = .ok (body, genv) →
      Func.traceCall (Step A) M U g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s₂)) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ (t₀ ++ t)
        (U + δ + 1)

omit [DecidableEq Mem] in
/-- The acts of a call before its callee show as many steps as the call
takes before its callee's, when every path of every op shows exactly one
step: none for a callee that its op names, the step of the rule that picks
the callee otherwise. -/
theorem Func.TCallsAt.ticks {o : Operation d}
    {args : HVector toType (sig o.op)} {s s₁ : TraceState Mem unit} {n n' : Nat} {sym : Name}
    {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)}
    (h : Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁)
    (hone : OpsOneStep d A (TraceState Mem unit)) : Step.ticks t₀ = n - n' := by
  cases h with
  | fixed _ => simp [Step.ticks]
  | picked _ hs =>
    have := hone.2.2 _ _ _ _ _ hs
    simp only [TraceEnd.trace] at this
    omega

/-! # Moves go on, run out of fuel, and hit UB -/

/-- A run with no fuel runs out of fuel after no marked trace. -/
theorem TCfg.exh_zero (c : TCfg d Mem unit) : c.exh A M 0 [] :=
  ⟨c.s, Func.traceOps_zero.2 rfl⟩

/-- A move of a configuration is a move of the paths of its run that run out
of fuel, when every path of every op shows exactly one step. -/
theorem TCfg.Move.tStep (hone : OpsOneStep d A (TraceState Mem unit)) {c c₁ : TCfg d Mem unit}
    {t : List (Step A)} {F : Nat} (h : TCfg.Move A M c c₁ t F) :
    TStep (c.exh A M) (c₁.exh A M) t F := by
  have zero : ∀ {F : Nat} (t : List (Step A)), 0 < F →
      (0 < F ∧ ∃ mt, c.exh A M 0 mt ∧ mt <+: t) := fun _ hF => ⟨hF, [], c.exh_zero, List.nil_prefix⟩
  have one : ∀ {δ : Nat}, δ ≤ 1 →
      (∀ n₁ (mt₁ : List (Step A)), c₁.exh A M n₁ mt₁ → c.exh A M (n₁ + δ + 1) (t ++ mt₁)) →
      (0 < δ → ∃ mt, c.exh A M 1 mt ∧ mt <+: t) →
      Step.ticks t ≤ δ + 1 → TStep (c.exh A M) (c₁.exh A M) t (δ + 1) := fun {δ} hδ hgo hlow ht =>
    ⟨ht, fun n => match n with
      | 0 => .inl (zero t (Nat.succ_pos _))
      | n₁ + 1 => by
        by_cases hn : δ ≤ n₁
        · refine .inr ⟨n₁ - δ, by omega, by omega, fun mt₁ h₁ => ?_⟩
          have := hgo _ _ h₁
          rwa [Nat.sub_add_cancel hn] at this
        · obtain ⟨mt, hmt, hp⟩ := hlow (by omega)
          obtain rfl : n₁ = 0 := by omega
          exact .inl ⟨by omega, mt, hmt, hp⟩⟩
  -- With no step left for the call, the rule that picks the callee runs out of fuel.
  have low : ∀ {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s : TraceState Mem unit} {args : HVector toType (sig o.op)} {δ : Nat} {sym : Name}
      {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)}
      {s₁ : TraceState Mem unit},
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ → 0 < δ →
      TCfg.exh A M ⟨f, env, o :: os, s⟩ 1 t₀ := fun hreg hargs hT hc hδ => by
    obtain ⟨hpc, hs⟩ := hc.picked_of_lt hδ
    exact ⟨_, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2 (.pickExh hreg hargs hT hpc hs rfl)⟩
  cases h with
  | denote hreg hargs hT hc hx hlen =>
    refine one (δ := 0) (Nat.zero_le _) (fun n₁ mt₁ ⟨s₂, h₁⟩ =>
      ⟨s₂, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
        (.denote hreg hargs hT hc hx hlen h₁)⟩) (fun h => absurd h (Nat.lt_irrefl _)) ?_
    have := (hone.1 _ _ _).1 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | ext hreg hargs hT hc hg hd hx hty hlen =>
    have ht₀ := hc.ticks hone
    have hδ := hc.le
    refine one (by omega) (fun n₁ mt₁ ⟨s₂, h₁⟩ => ⟨s₂, ?_⟩)
      (fun hδ => ⟨_, low hreg hargs hT hc hδ, List.prefix_append _ _⟩) ?_
    · rw [List.append_assoc]
      exact (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
        (.ext hreg hargs hT (hc.at n₁) hg hd hx hty hlen h₁)
    · have := hone.2.1 _ _ _ _ _ hx
      simp only [TraceEnd.trace] at this
      rw [Step.ticks_append]
      omega
  | goto hreg hargs hT hos hx hj =>
    refine one (δ := 0) (Nat.zero_le _) (fun n₁ mt₁ ⟨s₂, h₁⟩ =>
      ⟨s₂, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
        (.goto hreg hargs hT hos hx hj h₁)⟩) (fun h => absurd h (Nat.lt_irrefl _)) ?_
    have := (hone.1 _ _ _).2 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | enter hreg hargs hT hc hg hen =>
    have ht₀ := hc.ticks hone
    have hδ := hc.le
    refine one (by omega) (fun n₁ mt₁ ⟨s₂, h₁⟩ => ⟨_, (Func.tStepPath_iff
      (TraceEnd.notStuck_ok _ _ _)).2 (.callExh hreg hargs hT (hc.at n₁) hg hen
        ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩))⟩)
      (fun hδ => ⟨_, low hreg hargs hT hc hδ, List.prefix_refl _⟩) (by omega)
  | @ret f env o os s s₁ s₂ args δ sym ts cargs t₀ g body genv U k vs t hreg hargs hT hc hg hen hx
      hty hlen =>
    have hpace := Func.traceCall_retPaced hone hx
    have ht₀ := hc.ticks hone
    have hδ := hc.le
    have rest : ∀ {N k' : Nat}, Func.traceCall (Step A) M N g genv body s₁
        (.ok (.ok (.ret (vs, k')), t, s₂)) → ∀ mt₁,
        TCfg.exh A M ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ (min k' N) mt₁ →
        TCfg.exh A M ⟨f, env, o :: os, s⟩ (N + δ + 1) (t₀ ++ t ++ mt₁) := fun {N _} hN mt₁ ⟨s₃, h₁⟩ =>
      ⟨s₃, by
        rw [List.append_assoc]
        exact (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
          (.callRet hreg hargs hT (hc.at N) hg hen hN hty hlen h₁)⟩
    refine ⟨by rw [Step.ticks_append]; omega, fun n => ?_⟩
    match n with
    | 0 => exact .inl (zero _ (Nat.succ_pos _))
    | n₁ + 1 =>
    by_cases hn : δ ≤ n₁
    case neg =>
      obtain rfl : n₁ = 0 := by omega
      exact .inl ⟨by omega, t₀, low hreg hargs hT hc (by omega), List.prefix_append _ _⟩
    obtain ⟨n', rfl⟩ : ∃ n', n₁ = n' + δ := ⟨n₁ - δ, by omega⟩
    rcases Nat.lt_or_ge n' U with hn' | hn'
    · obtain ⟨W, hpos, hW⟩ := M.exists_callBound
      rcases Func.traceCall_cut_ret hone hW hpos (Nat.le_of_lt hn') hx with
        ⟨-, hr⟩ | ⟨-, t₁, s₀, hp, -, -, he⟩
      · exact .inr ⟨_, by have := Nat.min_le_right (k - (U - n')) n'; omega, by omega, rest hr⟩
      · exact .inl ⟨by omega, t₀ ++ t₁, ⟨_, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
          (.callExh hreg hargs hT (hc.at n') hg hen he)⟩,
          (List.prefix_append_right_inj t₀).2 hp⟩
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn'
      have hup := Func.traceCall_up b U hx trivial
      refine .inr ⟨min (k + b) (U + b), by omega, by omega, fun mt₁ h₁ => ?_⟩
      exact rest hup mt₁ h₁

/-- UB of the configuration a move goes on to is UB of the configuration,
after the move's marked trace. -/
theorem TCfg.Move.ub {c c₁ : TCfg d Mem unit} {t : List (Step A)} {F : Nat}
    (h : TCfg.Move A M c c₁ t F) {n : Nat} {r : String} {mt₁ : List (Step A)}
    (h₁ : c₁.ub A M n r mt₁) : ∃ n', c.ub A M n' r (t ++ mt₁) := by
  have mk : ∀ {N} {o : Operation d} {os : List (Operation d)} {f : Func d} {env : Env d}
      {s : TraceState Mem unit} {tr : List (Step A)}, Func.TStepPath M N f env o os s (.error (r, tr)) →
      Func.traceOps (Step A) M (N + 1) f env (o :: os) s (.error (r, tr)) :=
    fun hp => (Func.tStepPath_iff (TraceEnd.notStuck_error _ _)).2 hp
  cases h with
  | denote hreg hargs hT hc hx hlen => exact ⟨_, mk (.denote hreg hargs hT hc hx hlen h₁)⟩
  | ext hreg hargs hT hc hg hd hx hty hlen =>
    have := mk (.ext hreg hargs hT (hc.at n) hg hd hx hty hlen h₁)
    rw [← List.append_assoc] at this
    exact ⟨_, this⟩
  | goto hreg hargs hT hos hx hj => exact ⟨_, mk (.goto hreg hargs hT hos hx hj h₁)⟩
  | enter hreg hargs hT hc hg hen =>
    exact ⟨_, mk (.callUB hreg hargs hT (hc.at n) hg hen ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩))⟩
  | @ret _ _ o os s s₁ s₂ args δ sym ts cargs t₀ g body genv U k vs t hreg hargs hT hc hg hen hx
      hty hlen =>
    have hup := Func.traceCall_up n U hx trivial
    have hrest := Func.traceOps_up (min (k + n) (U + n) - n) n _ _ _ _ _ h₁ trivial
    rw [Nat.add_sub_cancel' (by omega)] at hrest
    have := mk (.callRet hreg hargs hT (hc.at (U + n)) hg hen hup hty hlen hrest)
    rw [← List.append_assoc] at this
    exact ⟨_, this⟩

/-- A move that shows no step enters a callee: the ops it goes on to are the
entry block of the callee of its configuration's first op. -/
theorem TCfg.Move.callHead (hone : OpsOneStep d A (TraceState Mem unit)) {c c₁ : TCfg d Mem unit}
    {t : List (Step A)} {F : Nat} (h : TCfg.Move A M c c₁ t F) (ht : Step.ticks t = 0) :
    M.callHead? c.os = some c₁.os := by
  cases h with
  | denote _ _ _ _ hx =>
    have := (hone.1 _ _ _).1 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | ext _ _ _ _ _ _ hx =>
    have := hone.2.1 _ _ _ _ _ hx
    simp only [TraceEnd.trace] at this
    rw [Step.ticks_append] at ht
    omega
  | goto _ _ _ _ hx =>
    have := (hone.1 _ _ _).2 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | enter _ _ hT hc hg hen =>
    cases hc with
    | fixed hc => exact Module.callHead?_call _ hT hc hg hen
    | picked _ hs =>
      have := hone.2.2 _ _ _ _ _ hs
      simp only [TraceEnd.trace] at this
      omega
  | ret _ _ _ _ _ _ hx =>
    have := (Func.traceCall_retPaced hone hx).2
    rw [Step.ticks_append] at ht
    omega

end Fir
