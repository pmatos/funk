import Fir.Execution.TraceBranch
import Fir.Execution.TraceAhead
import Fir.Execution.TraceTruncate

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
* a call that enters its callee: no marked trace of its own, and one step of
  fuel;
* a call whose callee returns at the budget `U`: the callee's marked trace,
  and `U + 1` steps of fuel.

Each move is a move of the runs' paths that run out of fuel (`TCfg.Move.tStep`,
`Fir.Execution.TraceBranch`). With fuel enough, the configuration goes on
after the move's marked trace by every path of the next one; below the
move's fuel it runs out of fuel within the move. For a callee that returns,
more fuel lets it return with more steps left (`Func.traceCall_up`), and less
cuts it (`Func.traceOps_cut`), in the module whose chains of calls are
bounded. UB of the next configuration is UB of the configuration, after the
move's marked trace (`TCfg.Move.ub`). Only a move that enters a callee shows
no step, and it goes one call along the chain of calls of the ops
(`TCfg.Move.callHead`).
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
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] {M : Module d}

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
  | goto {f : Func d} {env env₁ : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)} {i : Nat} {t : List (Step A)}
      {b : Block d} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM (Step A) (TraceState Mem unit)) o.op args s (.ok (.goto i, t, s₁)) →
      f.jump env o.succs i = .ok (b, env₁) →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨f, env₁, b.body, s₁⟩ t 1
  | enter {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s : TraceState Mem unit} {args : HVector toType (sig o.op)} {sym : Name} {g : Func d}
      {body : List (Operation d)} {genv : Env d} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some sym → M.func? sym = some g →
      g.enter args.toDVals = .ok (body, genv) →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨g, genv, body, { s with mem := s.mem.enter }⟩ [] 1
  | ret {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)} {sym : Name} {g : Func d}
      {body : List (Operation d)} {genv : Env d} {U k : Nat} {vs : List (DVal d)} {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some sym → M.func? sym = some g →
      g.enter args.toDVals = .ok (body, genv) →
      Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁)) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      TCfg.Move M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₁⟩ t (U + 1)

/-! # A callee's return, cut and paced -/

/-- A return of a callee's ops in its frame leaves at least as many steps as
its marked trace, and shows a step, when every path of every op shows exactly
one step. -/
theorem Func.traceCall_retPaced (hone : OpsOneStep d A (TraceState Mem unit)) {U k : Nat}
    {g : Func d} {genv : Env d} {body : List (Operation d)} {s s₁ : TraceState Mem unit}
    {vs : List (DVal d)} {t : List (Step A)}
    (h : Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁))) :
    k + Step.ticks t ≤ U ∧ 0 < Step.ticks t := by
  obtain ⟨W, -, hW⟩ := M.exists_callBound
  obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 h
  rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
  · cases he₁
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
  obtain ⟨rfl, rfl, -⟩ := he₁
  obtain ⟨hk, hp, -⟩ := Func.traceOps_retPaced A hone hW U _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
  exact ⟨hk, hp⟩

/-- A return of a callee's ops in its frame takes at most `W` steps of fuel for
each of its steps, when `W` exceeds the length of every chain of calls of the
module by at least one. -/
theorem Func.traceCall_retPaced_le (hone : OpsOneStep d A (TraceState Mem unit)) {W : Nat}
    (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W) {U k : Nat} {g : Func d} {genv : Env d}
    {body : List (Operation d)} {s s₁ : TraceState Mem unit} {vs : List (DVal d)}
    {t : List (Step A)}
    (h : Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁))) :
    U ≤ k + W * Step.ticks t := by
  obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 h
  rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
  · cases he₁
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
  obtain ⟨rfl, rfl, -⟩ := he₁
  obtain ⟨-, -, c, hc, hb⟩ :=
    Func.traceOps_retPaced A hone hW U _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
  have := hW _ _ hc
  omega

/-- A return of a callee's ops in its frame at the budget `U`, cut to a smaller
budget `n`, returns there with as many fewer steps left, when it left at least
`U - n`; otherwise the callee runs out of fuel at `n`, truncated: after a
marked trace that starts its own, of at most `n` steps, that is all of its own
or has `n ≤ W m + c`, for its `m` steps and a chain of `c` calls. -/
theorem Func.traceCall_cut_ret (hone : OpsOneStep d A (TraceState Mem unit)) {W : Nat}
    (hW : ∀ os c, M.CallChain os c → c + 1 ≤ W) (hpos : 0 < W) {U n k : Nat}
    (hn : n ≤ U) {g : Func d} {genv : Env d} {body : List (Operation d)} {s s₁ : TraceState Mem unit}
    {vs : List (DVal d)} {t : List (Step A)}
    (h : Func.traceCall (Step A) M U g genv body s (.ok (.ok (.ret (vs, k)), t, s₁))) :
    (U - n ≤ k ∧
      Func.traceCall (Step A) M n g genv body s (.ok (.ok (.ret (vs, k - (U - n))), t, s₁))) ∨
    (k < U - n ∧ ∃ t₀ s₀, t₀ <+: t ∧ Step.ticks t₀ ≤ n ∧
      (t₀ = t ∨ ∃ c, M.CallChain body c ∧ n ≤ W * Step.ticks t₀ + c) ∧
      Func.traceCall (Step A) M n g genv body s (.ok (.ok .fuelExhausted, t₀, s₀))) := by
  obtain ⟨e₁, h₁, he₁⟩ := (TraceM.run_inFrame _ _ _).1 h
  rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
  · cases he₁
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
  obtain ⟨rfl, rfl, rfl⟩ := he₁
  rw [← Nat.add_sub_cancel' hn] at h₁
  obtain ⟨e, he, hcut⟩ := Func.traceOps_cut A hone hW hpos n (U - n) _ _ _ _ _ h₁
    (TraceEnd.notStuck_ok _ _ _)
  rcases hcut with ⟨hj, rfl⟩ | ⟨hk, t₀, s₀, rfl, hp, ht₀, hb⟩
  · exact .inl ⟨hj, (TraceM.run_inFrame _ _ _).2 ⟨_, he, rfl⟩⟩
  · exact .inr ⟨hk, t₀, _, hp, ht₀, hb, (TraceM.run_inFrame _ _ _).2 ⟨_, he, rfl⟩⟩

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
  have one : (∀ n₁ (mt₁ : List (Step A)), c₁.exh A M n₁ mt₁ → c.exh A M (n₁ + 1) (t ++ mt₁)) →
      Step.ticks t ≤ 1 → TStep (c.exh A M) (c₁.exh A M) t 1 := fun hgo ht =>
    ⟨ht, fun n => match n with
      | 0 => .inl (zero t Nat.one_pos)
      | n₁ + 1 => .inr ⟨n₁, Nat.lt_succ_self _, Nat.le_refl _, hgo n₁⟩⟩
  cases h with
  | denote hreg hargs hT hc hx hlen =>
    refine one (fun n₁ mt₁ ⟨s₂, h₁⟩ => ⟨s₂, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
      (.denote hreg hargs hT hc hx hlen h₁)⟩) ?_
    have := (hone _ _ _).1 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | goto hreg hargs hT hos hx hj =>
    refine one (fun n₁ mt₁ ⟨s₂, h₁⟩ => ⟨s₂, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
      (.goto hreg hargs hT hos hx hj h₁)⟩) ?_
    have := (hone _ _ _).2 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | enter hreg hargs hT hc hg hen =>
    refine one (fun n₁ mt₁ ⟨s₂, h₁⟩ => ⟨_, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
      (.callExh hreg hargs hT hc hg hen ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩))⟩) ?_
    simp [Step.ticks]
  | @ret f env o os s s₁ args sym g body genv U k vs t hreg hargs hT hc hg hen hx hty hlen =>
    have hpace := Func.traceCall_retPaced hone hx
    have rest : ∀ {N k' : Nat}, Func.traceCall (Step A) M N g genv body s
        (.ok (.ok (.ret (vs, k')), t, s₁)) → ∀ mt₁,
        TCfg.exh A M ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₁⟩ (min k' N) mt₁ →
        TCfg.exh A M ⟨f, env, o :: os, s⟩ (N + 1) (t ++ mt₁) := fun hN mt₁ ⟨s₂, h₁⟩ =>
      ⟨s₂, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
        (.callRet hreg hargs hT hc hg hen hN hty hlen h₁)⟩
    refine ⟨by omega, fun n => ?_⟩
    rcases Nat.lt_or_ge n (U + 1) with hn | hn
    · match n, hn with
      | 0, _ => exact .inl (zero t (Nat.succ_pos _))
      | n' + 1, hn =>
        obtain ⟨W, hpos, hW⟩ := M.exists_callBound
        rcases Func.traceCall_cut_ret hone hW hpos (by omega : n' ≤ U) hx with
          ⟨-, hr⟩ | ⟨-, t₀, s₀, hp, -, -, he⟩
        · exact .inr ⟨_, Nat.lt_succ_of_le (Nat.min_le_right _ _), by omega, rest hr⟩
        · exact .inl ⟨hn, t₀, ⟨_, (Func.tStepPath_iff (TraceEnd.notStuck_ok _ _ _)).2
            (.callExh hreg hargs hT hc hg hen he)⟩, hp⟩
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hup := Func.traceCall_up b U hx trivial
      refine .inr ⟨min (k + b) (U + b), by omega, by omega, fun mt₁ h₁ => ?_⟩
      have := rest hup mt₁ h₁
      rwa [Nat.add_right_comm] at this

/-- UB of the configuration a move goes on to is UB of the configuration,
after the move's marked trace. -/
theorem TCfg.Move.ub {c c₁ : TCfg d Mem unit} {t : List (Step A)} {F : Nat}
    (h : TCfg.Move A M c c₁ t F) {n : Nat} {r : String} {mt₁ : List (Step A)}
    (h₁ : c₁.ub A M n r mt₁) : ∃ n', c.ub A M n' r (t ++ mt₁) := by
  have mk : ∀ {N} {o : Operation d} {os : List (Operation d)} {f : Func d} {env : Env d}
      {s : TraceState Mem unit}, Func.TStepPath M N f env o os s (.error (r, t ++ mt₁)) →
      Func.traceOps (Step A) M (N + 1) f env (o :: os) s (.error (r, t ++ mt₁)) :=
    fun hp => (Func.tStepPath_iff (TraceEnd.notStuck_error _ _)).2 hp
  cases h with
  | denote hreg hargs hT hc hx hlen => exact ⟨_, mk (.denote hreg hargs hT hc hx hlen h₁)⟩
  | goto hreg hargs hT hos hx hj => exact ⟨_, mk (.goto hreg hargs hT hos hx hj h₁)⟩
  | enter hreg hargs hT hc hg hen =>
    exact ⟨_, mk (.callUB hreg hargs hT hc hg hen ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩))⟩
  | @ret _ _ o os s s₁ args sym g body genv U k vs t hreg hargs hT hc hg hen hx hty hlen =>
    have hup := Func.traceCall_up n U hx trivial
    have hrest := Func.traceOps_up (min (k + n) (U + n) - n) n _ _ _ _ _ h₁ trivial
    rw [Nat.add_sub_cancel' (by omega)] at hrest
    exact ⟨_, mk (.callRet hreg hargs hT hc hg hen hup hty hlen hrest)⟩

/-- A move that shows no step enters a callee: the ops it goes on to are the
entry block of the callee of its configuration's first op. -/
theorem TCfg.Move.callHead (hone : OpsOneStep d A (TraceState Mem unit)) {c c₁ : TCfg d Mem unit}
    {t : List (Step A)} {F : Nat} (h : TCfg.Move A M c c₁ t F) (ht : Step.ticks t = 0) :
    M.callHead? c.os = some c₁.os := by
  cases h with
  | denote _ _ _ _ hx =>
    have := (hone _ _ _).1 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | goto _ _ _ _ hx =>
    have := (hone _ _ _).2 _ hx
    simp only [TraceEnd.trace] at this
    omega
  | enter _ _ hT hc hg hen => exact Module.callHead?_call _ hT hc hg hen
  | ret _ _ _ _ _ _ hx =>
    have := (Func.traceCall_retPaced hone hx).2
    omega

end Fir
