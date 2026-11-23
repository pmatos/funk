import Fir.Execution.MemoryPathsFrom

/-!
# A run of ops with memory, one step at a time

The refinement proofs compare two runs path by path: they follow each path
of one run, and find a path of the other that allows it (the section on a
run of ops, one step at a time). This section says, once, every way in
which a path of a run of ops with memory goes on from its first op, read
from given memories (the section on how a run with memory ends):

* A path that does not end stuck, with fuel left and an op to run, takes
  one of the eleven ways of a run in the set monad, each from the memories
  that the run starts from. A terminator's exit or an op's rule ends from
  them, in UB or with the memories after it, from which the run goes on;
  an external call is UB with memory too. A
  call runs its callee in a frame: from them with a new frame entered, and
  each return leaves the frame. When the callee returns, the caller goes
  on, with the steps that the callee leaves, from the memories that the
  callee's return ends with.
* A run with no fuel runs out of fuel, and a block with no op left is
  stuck.
-/

namespace Fir

open SetM Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-! # The ways a step goes on -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-- The op `o`, on the operands `args`, from the memories `S`, with `n`
steps left after its own, calls the symbol `s` on the arguments `cargs`, of
the types `ts`, with `n'` steps left for the call, from the memories `S₁`:
a callee that `o` names, on its operands, from `S`, with the steps that `o`
leaves; or one that its rule picks, on its operands but the first, from the
memories that the rule ends with, after one more step, the call's
(#235). -/
inductive Func.MemCallsAt (M : Module d) (o : Operation d) (args : HVector toType (sig o.op))
    (S : Memories Mem unit) :
    Nat → Name → (ts : List d.Ty) → HVector toType ts → Nat → Memories Mem unit → Prop
  | fixed {n : Nat} {s : Name} : callee? o.op = some (.fixed s) →
      Func.MemCallsAt M o args S n s (sig o.op) args n S
  | picked {n : Nat} {s : Name} {S₁ : Memories Mem unit} : callee? o.op = some .picked →
      DialectDenote.pick (m := StateT (Memories Mem unit) SetM) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args S (.ok (s, S₁)) →
      Func.MemCallsAt M o args S (n + 1) s (sig o.op).tail args.tail n S₁

/-- The ways a path of a run with memory of the ops `o :: os` of `f`, with
`n + 1` steps, from the memories `S`, goes on, when it does not end
stuck. -/
inductive Func.MemStepPath (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (S : Memories Mem unit) :
    Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat))) → Prop
  | exitUB {args : HVector toType (sig o.op)} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args S (.ub r) →
      Func.MemStepPath M n f env o os S (.ub r)
  | ret {args : HVector toType (sig o.op)} {S' : Memories Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args S (.ok (.ret, S')) →
      sig o.op = f.results → Func.MemStepPath M n f env o os S (.ok (.ok (.ret ((args.toDVals, S'), n))))
  | goto {args : HVector toType (sig o.op)} {i : Nat} {S' : Memories Mem unit} {b : Block d}
      {env₁ : Env d} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args S (.ok (.goto i, S')) →
      f.jump env o.succs i = .ok (b, env₁) → (Func.memOps M n f env₁ b.body S').run e →
      Func.MemStepPath M n f env o os S e
  | denoteUB {args : HVector toType (sig o.op)} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := StateT (Memories Mem unit) SetM) o.op args S (.ub r) →
      Func.MemStepPath M n f env o os S (.ub r)
  | denote {args : HVector toType (sig o.op)} {rs : HVector toType (returnTypes o.op)}
      {S' : Memories Mem unit} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := StateT (Memories Mem unit) SetM) o.op args S (.ok (rs, S')) →
      (o.results.map (·.1)).length = rs.toDVals.length →
      (Func.memOps M n f ((o.results.map (·.1)).zip rs.toDVals ++ env) os S').run e →
      Func.MemStepPath M n f env o os S e
  | callUB {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {S₁ : Memories Mem unit} {g : Func d} {body genv}
      {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.MemCallsAt M o args S n s ts cargs n' S₁ →
      M.func? s = some g → g.enter cargs.toDVals = .ok (body, genv) →
      (Func.memCall M n' g genv body S₁).run (.ub r) → Func.MemStepPath M n f env o os S (.ub r)
  | callExh {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {S₁ : Memories Mem unit} {g : Func d} {body genv} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.MemCallsAt M o args S n s ts cargs n' S₁ →
      M.func? s = some g → g.enter cargs.toDVals = .ok (body, genv) →
      (Func.memCall M n' g genv body S₁).run (.ok (.ok .fuelExhausted)) →
      Func.MemStepPath M n f env o os S (.ok (.ok .fuelExhausted))
  | callRet {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {S₁ : Memories Mem unit} {g : Func d} {body genv}
      {vs : List (DVal d)} {S' : Memories Mem unit} {k : Nat} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.MemCallsAt M o args S n s ts cargs n' S₁ →
      M.func? s = some g → g.enter cargs.toDVals = .ok (body, genv) →
      (Func.memCall M n' g genv body S₁).run (.ok (.ok (.ret ((vs, S'), k)))) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      (Func.memOps M (min k n') f ((o.results.map (·.1)).zip vs ++ env) os S').run e →
      Func.MemStepPath M n f env o os S e
  | extUB {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {S₁ : Memories Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.MemCallsAt M o args S n s ts cargs n' S₁ →
      M.func? s = none → M.declares s ts (returnTypes o.op) = true →
      Func.MemStepPath M n f env o os S (.ub extCallUB)
  | pickUB {args : HVector toType (sig o.op)} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some .picked →
      DialectDenote.pick (m := StateT (Memories Mem unit) SetM) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args S (.ub r) →
      Func.MemStepPath M n f env o os S (.ub r)
  | pickExh {args : HVector toType (sig o.op)} {s : Name} {S₁ : Memories Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some .picked →
      DialectDenote.pick (m := StateT (Memories Mem unit) SetM) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args S (.ok (s, S₁)) → n = 0 →
      Func.MemStepPath M n f env o os S (.ok (.ok .fuelExhausted))

/-- A path of a run of ops with memory that is not stuck, from `S`, is a
path that the first op goes on by, and every such path is a path of the
run. -/
theorem Func.memStepPath_iff {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {o : Operation d} {os : List (Operation d)} {S : Memories Mem unit}
    {e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (hne : Ev.NotStuck e) :
    (Func.memOps M (n + 1) f env (o :: os) S).run e ↔ Func.MemStepPath M n f env o os S e := by
  constructor
  · intro h
    simp only [Func.memOps, Func.runOps] at h
    split at h
    · obtain ⟨_, h, _⟩ := (runFrom_liftExcept_bind hne).1 h
      cases h
    rename_i hreg
    have hreg' : o.ownsCoreRegion = false := by simpa using hreg
    obtain ⟨args, hargs, h⟩ := (runFrom_liftExcept_bind hne).1 h
    split at h
    · rename_i hT
      split at h
      · obtain ⟨_, h, _⟩ := (runFrom_liftExcept_bind hne).1 h
        cases h
      rename_i hos
      have hos' : os = [] := by simpa using hos
      rcases runFrom_lift_bind.1 h with ⟨x, S', hx, h⟩ | ⟨r, hr, rfl⟩
      · cases x with
        | ret =>
          dsimp only at h
          split at h
          · rw [runFrom_ret] at h
            cases (run_pure _ _).1 h
            exact .ret hreg' hargs hT hos' hx (by assumption)
          · rw [runFrom_stuck] at h
            exact absurd ((run_liftExcept _ _).1 h) (hne _)
        | goto i =>
          dsimp only at h
          obtain ⟨⟨b, env₁⟩, hj, h⟩ := (runFrom_liftExcept_bind hne).1 h
          exact .goto hreg' hargs hT hos' hx hj h
      · exact .exitUB hreg' hargs hT hos' hr
    · rename_i hT
      have hT' : isTerminator o.op = false := by simpa using hT
      split at h
      · rename_i hc
        rcases runFrom_lift_bind.1 h with ⟨rs, S', hrs, h⟩ | ⟨r, hr, rfl⟩
        · obtain ⟨env₁, hb, h⟩ := (runFrom_liftExcept_bind hne).1 h
          simp only [Env.bind] at hb
          split at hb
          · cases hb
            exact .denote hreg' hargs hT' hc hrs (by assumption) h
          · cases hb
        · exact .denoteUB hreg' hargs hT' hc hr
      · rename_i s hc
        split at h
        · rename_i g hg
          obtain ⟨⟨body, genv⟩, hen, h⟩ := (runFrom_liftExcept_bind hne).1 h
          rcases (runFrom_bindRun (by rfl) hne).1 h with ⟨vs, S', k, hr, h⟩ | ⟨hr, rfl⟩ | ⟨u, hu, rfl⟩
          · dsimp only at h
            split at h
            · obtain ⟨env₁, hb, h⟩ := (runFrom_liftExcept_bind hne).1 h
              simp only [Env.bind] at hb
              split at hb
              · cases hb
                exact .callRet hreg' hargs hT' (.fixed hc) hg hen hr (by assumption) (by assumption) h
              · cases hb
            · rw [runFrom_stuck] at h
              exact absurd ((run_liftExcept _ _).1 h) (hne _)
          · exact .callExh hreg' hargs hT' (.fixed hc) hg hen hr
          · exact .callUB hreg' hargs hT' (.fixed hc) hg hen hu
        · rename_i hg
          split at h
          · rename_i hd
            rcases runFrom_lift_bind.1 h with ⟨_, _, hvs, _⟩ | ⟨r, hr, rfl⟩
            · cases (extCall_stateT_setM _ _ _ _ _).1 hvs
            · cases (extCall_stateT_setM _ _ _ _ _).1 hr
              exact .extUB hreg' hargs hT' (.fixed hc) hg hd
          · rw [runFrom_stuck] at h
            exact absurd ((run_liftExcept _ _).1 h) (hne _)
      · rename_i hc
        rcases runFrom_lift_bind.1 h with ⟨s, S₁, hs, h⟩ | ⟨r, hr, rfl⟩
        · cases n with
          | zero =>
            dsimp only at h
            rw [runFrom_exhausted] at h
            cases (run_pure _ _).1 h
            exact .pickExh hreg' hargs hT' hc hs rfl
          | succ n =>
            dsimp only at h
            split at h
            · rename_i g hg
              obtain ⟨⟨body, genv⟩, hen, h⟩ := (runFrom_liftExcept_bind hne).1 h
              rcases (runFrom_bindRun (by rfl) hne).1 h with ⟨vs, S', k, hr, h⟩ | ⟨hr, rfl⟩ | ⟨u, hu, rfl⟩
              · dsimp only at h
                split at h
                · obtain ⟨env₁, hb, h⟩ := (runFrom_liftExcept_bind hne).1 h
                  simp only [Env.bind] at hb
                  split at hb
                  · cases hb
                    exact .callRet hreg' hargs hT' (.picked hc hs) hg hen hr (by assumption) (by assumption) h
                  · cases hb
                · rw [runFrom_stuck] at h
                  exact absurd ((run_liftExcept _ _).1 h) (hne _)
              · exact .callExh hreg' hargs hT' (.picked hc hs) hg hen hr
              · exact .callUB hreg' hargs hT' (.picked hc hs) hg hen hu
            · rename_i hg
              split at h
              · rename_i hd
                rcases runFrom_lift_bind.1 h with ⟨_, _, hvs, _⟩ | ⟨r, hr, rfl⟩
                · cases (extCall_stateT_setM _ _ _ _ _).1 hvs
                · cases (extCall_stateT_setM _ _ _ _ _).1 hr
                  exact .extUB hreg' hargs hT' (.picked hc hs) hg hd
              · rw [runFrom_stuck] at h
                exact absurd ((run_liftExcept _ _).1 h) (hne _)
        · exact .pickUB hreg' hargs hT' hc hr
  · intro h
    simp only [Func.memOps, Func.runOps]
    cases h with
    | exitUB hreg hargs hT hos hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact runFrom_lift_bind.2 (.inr ⟨_, hx, rfl⟩)
    | ret hreg hargs hT hos hx hs =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      refine runFrom_lift_bind.2 (.inl ⟨_, _, hx, ?_⟩)
      dsimp only
      rw [ite_eq_left hs, runFrom_ret]
      exact (run_pure _ _).2 rfl
    | goto hreg hargs hT hos hx hj h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact runFrom_lift_bind.2 (.inl ⟨_, _, hx, (runFrom_liftExcept_bind hne).2 ⟨_, hj, h⟩⟩)
    | denoteUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact runFrom_lift_bind.2 (.inr ⟨_, hx, rfl⟩)
    | denote hreg hargs hT hc hx hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact runFrom_lift_bind.2
        (.inl ⟨_, _, hx, (runFrom_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩⟩)
    | callUB hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        exact (runFrom_liftExcept_bind hne).2 ⟨_, hen,
          (runFrom_bindRun (by rfl) hne).2 (.inr (.inr ⟨_, hx, rfl⟩))⟩
      | picked hc hs =>
        simp only [hc]
        refine runFrom_lift_bind.2 (.inl ⟨_, _, hs, ?_⟩)
        simp only [hg]
        exact (runFrom_liftExcept_bind hne).2 ⟨_, hen,
          (runFrom_bindRun (by rfl) hne).2 (.inr (.inr ⟨_, hx, rfl⟩))⟩
    | callExh hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        exact (runFrom_liftExcept_bind hne).2 ⟨_, hen,
          (runFrom_bindRun (by rfl) hne).2 (.inr (.inl ⟨hx, rfl⟩))⟩
      | picked hc hs =>
        simp only [hc]
        refine runFrom_lift_bind.2 (.inl ⟨_, _, hs, ?_⟩)
        simp only [hg]
        exact (runFrom_liftExcept_bind hne).2 ⟨_, hen,
          (runFrom_bindRun (by rfl) hne).2 (.inr (.inl ⟨hx, rfl⟩))⟩
    | callRet hreg hargs hT hc hg hen hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        refine (runFrom_liftExcept_bind hne).2 ⟨_, hen,
          (runFrom_bindRun (by rfl) hne).2 (.inl ⟨_, _, _, hx, ?_⟩)⟩
        dsimp only
        rw [ite_eq_left hty]
        exact (runFrom_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩
      | picked hc hs =>
        simp only [hc]
        refine runFrom_lift_bind.2 (.inl ⟨_, _, hs, ?_⟩)
        simp only [hg]
        refine (runFrom_liftExcept_bind hne).2 ⟨_, hen,
          (runFrom_bindRun (by rfl) hne).2 (.inl ⟨_, _, _, hx, ?_⟩)⟩
        dsimp only
        rw [ite_eq_left hty]
        exact (runFrom_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩
    | extUB hreg hargs hT hc hg hd =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        simp only [hd, ↓reduceIte]
        exact runFrom_lift_bind.2 (.inr ⟨_, (extCall_stateT_setM _ _ _ _ _).2 rfl, rfl⟩)
      | picked hc hs =>
        simp only [hc]
        refine runFrom_lift_bind.2 (.inl ⟨_, _, hs, ?_⟩)
        simp only [hg, hd, ↓reduceIte]
        exact runFrom_lift_bind.2 (.inr ⟨_, (extCall_stateT_setM _ _ _ _ _).2 rfl, rfl⟩)
    | pickUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact runFrom_lift_bind.2 (.inr ⟨_, hx, rfl⟩)
    | pickExh hreg hargs hT hc hs hn =>
      subst hn
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      refine runFrom_lift_bind.2 (.inl ⟨_, _, hs, ?_⟩)
      rw [runFrom_exhausted]
      exact (run_pure _ _).2 rfl

end Fir
