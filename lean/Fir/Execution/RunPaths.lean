import Fir.Execution.CallsAt
import Fir.Execution.Environment

/-!
# A run of ops, one step at a time

A compiler rewrites a program one function at a time: it simplifies a
callee, inlines it, or passes a defined value where the source passed
poison. Each rewrite is correct when the new code refines the old. The
sections from here to the core dialect's poison obligations prove that
refinement goes through calls: a call on arguments that refine others
refines the call on those others, and replacing a callee by a body that,
run in the new module, refines the old callee refines every caller,
recursion included. So a pass can be
checked one function at a time, and the whole program stays correct.

Those proofs compare two runs path by path: they follow each path of one
run, and find a path of the other that allows it. This section says,
once, every way in which a path of a run of ops goes on from its first
op, so that the proofs need not unfold the interpreter:

* A path that does not end stuck, with fuel left and an op to run, takes
  one of eleven ways. In each, the op owns no region of the core's kind and
  its operands are
  found. Then the op is a terminator, the last op of its block, whose
  exit hits UB, returns, or jumps to a block, where the run goes on with
  one step less; or it runs by its own rule, which hits UB, or gives
  results that bind, and the run goes on with one step less; or it calls
  a function, which the run finds in the module and enters, and the
  callee hits UB, runs out of fuel, or returns values of the call's
  result types, which bind, and the run goes on with the steps that the
  callee leaves; or it calls an external declaration, which is UB in the
  set monad, a layer with no world (`Fir.Execution.ExtCall`). A call's
  callee is a fixed symbol, or one that the op's rule picks when it runs
  (#235): that rule hits UB, or picks a symbol with no step left for the
  call, which runs out of fuel, or picks one that the run then calls as
  above, with one step less (`Func.CallsAt`).
* A run with no fuel runs out of fuel, and a block with no op left is
  stuck.
* A run that runs out of fuel runs out of fuel with fewer steps too. It
  takes the same path, and runs out sooner. On a call, the callee with
  fewer steps runs out of fuel too, or returns leaving as many fewer
  steps, and the caller then goes on with fewer.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- The ways a path of a run of the ops `o :: os` of `f`, with `n + 1`
steps, goes on, when it does not end stuck. -/
inductive Func.StepPath (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) : Ev (Except Stuck (Result (List (DVal d) × Nat))) → Prop
  | exitUB {args : HVector toType (sig o.op)} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := SetM) o.op args (.ub r) → Func.StepPath M n f env o os (.ub r)
  | ret {args : HVector toType (sig o.op)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := SetM) o.op args (.ok .ret) → sig o.op = f.results →
      Func.StepPath M n f env o os (.ok (.ok (.ret (args.toDVals, n))))
  | goto {args : HVector toType (sig o.op)} {i : Nat} {b : Block d} {env₁ : Env d} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := SetM) o.op args (.ok (.goto i)) →
      f.jump env o.succs i = .ok (b, env₁) → (Func.runOps (m := SetM) M n f env₁ b.body).run e →
      Func.StepPath M n f env o os e
  | denoteUB {args : HVector toType (sig o.op)} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := SetM) o.op args (.ub r) → Func.StepPath M n f env o os (.ub r)
  | denote {args : HVector toType (sig o.op)} {rs : HVector toType (returnTypes o.op)} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := SetM) o.op args (.ok rs) →
      (o.results.map (·.1)).length = rs.toDVals.length →
      (Func.runOps (m := SetM) M n f ((o.results.map (·.1)).zip rs.toDVals ++ env) os).run e →
      Func.StepPath M n f env o os e
  | callUB {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {g : Func d} {body genv} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.CallsAt M o args n s ts cargs n' → M.func? s = some g →
      g.enter cargs.toDVals = .ok (body, genv) →
      (Func.runOps (m := SetM) M n' g genv body).run (.ub r) → Func.StepPath M n f env o os (.ub r)
  | callExh {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {g : Func d} {body genv} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.CallsAt M o args n s ts cargs n' → M.func? s = some g →
      g.enter cargs.toDVals = .ok (body, genv) →
      (Func.runOps (m := SetM) M n' g genv body).run (.ok (.ok .fuelExhausted)) →
      Func.StepPath M n f env o os (.ok (.ok .fuelExhausted))
  | callRet {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {g : Func d} {body genv} {vs : List (DVal d)}
      {k : Nat} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.CallsAt M o args n s ts cargs n' → M.func? s = some g →
      g.enter cargs.toDVals = .ok (body, genv) →
      (Func.runOps (m := SetM) M n' g genv body).run (.ok (.ok (.ret (vs, k)))) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      (Func.runOps (m := SetM) M (min k n') f ((o.results.map (·.1)).zip vs ++ env) os).run e →
      Func.StepPath M n f env o os e
  | extUB {args : HVector toType (sig o.op)} {s : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.CallsAt M o args n s ts cargs n' → M.func? s = none →
      M.declares s ts (returnTypes o.op) = true →
      Func.StepPath M n f env o os (.ub extCallUB)
  | pickUB {args : HVector toType (sig o.op)} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some .picked →
      DialectDenote.pick (m := SetM) o.op (M.callable (sig o.op).tail (returnTypes o.op)) args
        (.ub r) →
      Func.StepPath M n f env o os (.ub r)
  | pickExh {args : HVector toType (sig o.op)} {s : Name} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some .picked →
      DialectDenote.pick (m := SetM) o.op (M.callable (sig o.op).tail (returnTypes o.op)) args
        (.ok s) → n = 0 →
      Func.StepPath M n f env o os (.ok (.ok .fuelExhausted))

/-- A path of a run of ops that is not stuck is a path that the first op
goes on by, and every such path is a path of the run. -/
theorem Func.stepPath_iff {M : Module d} {n : Nat} {f : Func d} {env : Env d} {o : Operation d}
    {os : List (Operation d)} {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (hne : Ev.NotStuck e) :
    (Func.runOps (m := SetM) M (n + 1) f env (o :: os)).run e ↔ Func.StepPath M n f env o os e := by
  constructor
  · intro h
    simp only [Func.runOps] at h
    split at h
    · obtain ⟨_, h, _⟩ := (run_liftExcept_bind hne).1 h
      cases h
    rename_i hreg
    have hreg' : o.ownsCoreRegion = false := by simpa using hreg
    obtain ⟨args, hargs, h⟩ := (run_liftExcept_bind hne).1 h
    split at h
    · rename_i hT
      split at h
      · obtain ⟨_, h, _⟩ := (run_liftExcept_bind hne).1 h
        cases h
      rename_i hos
      have hos' : os = [] := by simpa using hos
      rcases run_lift_bind.1 h with ⟨x, hx, h⟩ | ⟨r, hr, rfl⟩
      · cases x with
        | ret =>
          dsimp only at h
          split at h
          · cases (run_pure _ _).1 h
            exact .ret hreg' hargs hT hos' hx (by assumption)
          · exact absurd ((run_liftExcept _ _).1 h) (hne _)
        | goto i =>
          dsimp only at h
          obtain ⟨⟨b, env₁⟩, hj, h⟩ := (run_liftExcept_bind hne).1 h
          exact .goto hreg' hargs hT hos' hx hj h
      · exact .exitUB hreg' hargs hT hos' hr
    · rename_i hT
      have hT' : isTerminator o.op = false := by simpa using hT
      split at h
      · rename_i hc
        rcases run_lift_bind.1 h with ⟨rs, hrs, h⟩ | ⟨r, hr, rfl⟩
        · obtain ⟨env₁, hb, h⟩ := (run_liftExcept_bind hne).1 h
          simp only [Env.bind] at hb
          split at hb
          · cases hb
            exact .denote hreg' hargs hT' hc hrs (by assumption) h
          · cases hb
        · exact .denoteUB hreg' hargs hT' hc hr
      · rename_i s hc
        split at h
        · rename_i g hg
          obtain ⟨⟨body, genv⟩, hen, h⟩ := (run_liftExcept_bind hne).1 h
          rcases (run_bind _ _ _).1 h with ⟨r, hr, h⟩ | ⟨st, hst, rfl⟩ | ⟨u, hu, rfl⟩
          · match r, hr, h with
            | .fuelExhausted, hr, h =>
              cases (run_pure _ _).1 h
              exact .callExh hreg' hargs hT' (.fixed hc) hg hen hr
            | .ret (vs, k), hr, h =>
              dsimp only at h
              split at h
              · obtain ⟨env₁, hb, h⟩ := (run_liftExcept_bind hne).1 h
                simp only [Env.bind] at hb
                split at hb
                · cases hb
                  exact .callRet hreg' hargs hT' (.fixed hc) hg hen hr (by assumption) (by assumption) h
                · cases hb
              · exact absurd ((run_liftExcept _ _).1 h) (hne _)
          · exact absurd rfl (hne st)
          · exact .callUB hreg' hargs hT' (.fixed hc) hg hen hu
        · rename_i hg
          split at h
          · rename_i hd
            rcases run_lift_bind.1 h with ⟨_, hvs, _⟩ | ⟨r, hr, rfl⟩
            · cases hvs
            · cases hr
              exact .extUB hreg' hargs hT' (.fixed hc) hg hd
          · exact absurd ((run_liftExcept _ _).1 h) (hne _)
      · rename_i hc
        rcases run_lift_bind.1 h with ⟨s, hs, h⟩ | ⟨r, hr, rfl⟩
        · cases n with
          | zero =>
            dsimp only at h
            cases (run_pure _ _).1 h
            exact .pickExh hreg' hargs hT' hc hs rfl
          | succ n =>
            dsimp only at h
            split at h
            · rename_i g hg
              obtain ⟨⟨body, genv⟩, hen, h⟩ := (run_liftExcept_bind hne).1 h
              rcases (run_bind _ _ _).1 h with ⟨r, hr, h⟩ | ⟨st, hst, rfl⟩ | ⟨u, hu, rfl⟩
              · match r, hr, h with
                | .fuelExhausted, hr, h =>
                  cases (run_pure _ _).1 h
                  exact .callExh hreg' hargs hT' (.picked hc hs) hg hen hr
                | .ret (vs, k), hr, h =>
                  dsimp only at h
                  split at h
                  · obtain ⟨env₁, hb, h⟩ := (run_liftExcept_bind hne).1 h
                    simp only [Env.bind] at hb
                    split at hb
                    · cases hb
                      exact .callRet hreg' hargs hT' (.picked hc hs) hg hen hr (by assumption) (by assumption)
                        h
                    · cases hb
                  · exact absurd ((run_liftExcept _ _).1 h) (hne _)
              · exact absurd rfl (hne st)
              · exact .callUB hreg' hargs hT' (.picked hc hs) hg hen hu
            · rename_i hg
              split at h
              · rename_i hd
                rcases run_lift_bind.1 h with ⟨_, hvs, _⟩ | ⟨r, hr, rfl⟩
                · cases hvs
                · cases hr
                  exact .extUB hreg' hargs hT' (.picked hc hs) hg hd
              · exact absurd ((run_liftExcept _ _).1 h) (hne _)
        · exact .pickUB hreg' hargs hT' hc hr
  · intro h
    simp only [Func.runOps]
    cases h with
    | exitUB hreg hargs hT hos hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact run_lift_bind.2 (.inr ⟨_, hx, rfl⟩)
    | ret hreg hargs hT hos hx hs =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      refine run_lift_bind.2 (.inl ⟨_, hx, ?_⟩)
      dsimp only
      rw [ite_eq_left hs]
      exact (run_pure _ _).2 rfl
    | goto hreg hargs hT hos hx hj h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact run_lift_bind.2 (.inl ⟨_, hx, (run_liftExcept_bind hne).2 ⟨_, hj, h⟩⟩)
    | denoteUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact run_lift_bind.2 (.inr ⟨_, hx, rfl⟩)
    | pickExh hreg hargs hT hc hs hn =>
      subst hn
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact run_lift_bind.2 (.inl ⟨_, hs, (run_pure _ _).2 rfl⟩)
    | denote hreg hargs hT hc hx hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact run_lift_bind.2 (.inl ⟨_, hx, (run_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩⟩)
    | callUB hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        exact (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inr (.inr ⟨_, hx, rfl⟩))⟩
      | picked hc hs =>
        simp only [hc]
        refine run_lift_bind.2 (.inl ⟨_, hs, ?_⟩)
        simp only [hg]
        exact (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inr (.inr ⟨_, hx, rfl⟩))⟩
    | callExh hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        exact (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inl ⟨_, hx, rfl⟩)⟩
      | picked hc hs =>
        simp only [hc]
        refine run_lift_bind.2 (.inl ⟨_, hs, ?_⟩)
        simp only [hg]
        exact (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inl ⟨_, hx, rfl⟩)⟩
    | callRet hreg hargs hT hc hg hen hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        refine (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inl ⟨_, hx, ?_⟩)⟩
        dsimp only
        rw [ite_eq_left hty]
        exact (run_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩
      | picked hc hs =>
        simp only [hc]
        refine run_lift_bind.2 (.inl ⟨_, hs, ?_⟩)
        simp only [hg]
        refine (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inl ⟨_, hx, ?_⟩)⟩
        dsimp only
        rw [ite_eq_left hty]
        exact (run_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩
    | extUB hreg hargs hT hc hg hd =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        simp only [hd, ↓reduceIte]
        exact run_lift_bind.2 (.inr ⟨_, rfl, rfl⟩)
      | picked hc hs =>
        simp only [hc]
        refine run_lift_bind.2 (.inl ⟨_, hs, ?_⟩)
        simp only [hg, hd, ↓reduceIte]
        exact run_lift_bind.2 (.inr ⟨_, rfl, rfl⟩)
    | pickUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact run_lift_bind.2 (.inr ⟨_, hx, rfl⟩)

/-- A run with no fuel runs out of fuel, and only so. -/
theorem Func.run_runOps_zero {M : Module d} {f : Func d} {env : Env d} {os : List (Operation d)}
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))} :
    (Func.runOps (m := SetM) M 0 f env os).run e ↔ e = .ok (.ok .fuelExhausted) := by
  simp only [Func.runOps]; exact run_pure _ _

/-- A block with no op left is stuck. -/
theorem Func.run_runOps_nil {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))} (hne : Ev.NotStuck e) :
    ¬ (Func.runOps (m := SetM) M (n + 1) f env []).run e := by
  simp only [Func.runOps]
  exact fun h => hne _ ((run_liftExcept _ _).1 h)

end Fir
