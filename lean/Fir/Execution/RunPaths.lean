import Fir.Execution.Monotone
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
  one of eight ways. In each, the op owns no region of the core's kind and
  its operands are
  found. Then the op is a terminator, the last op of its block, whose
  exit hits UB, returns, or jumps to a block, where the run goes on with
  one step less; or it runs by its own rule, which hits UB, or gives
  results that bind, and the run goes on with one step less; or it calls
  a function, which the run finds in the module and enters, and the
  callee hits UB, runs out of fuel, or returns values of the call's
  result types, which bind, and the run goes on with the steps that the
  callee leaves.
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

/-- A way to end that is not stuck. -/
def Ev.NotStuck (e : Ev (Except Stuck α)) : Prop := ∀ st, e ≠ .ok (.error st)

/-- A path of `liftExcept x >>= g` that is not stuck goes on from the
value that `x` holds. -/
theorem run_liftExcept_bind {x : Except Stuck α} {g : α → ExceptT Stuck SetM β}
    {e : Ev (Except Stuck β)} (hne : Ev.NotStuck e) :
    (liftExcept x >>= g).run e ↔ ∃ a, x = .ok a ∧ (g a).run e := by
  rw [run_bind]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨st, hst, rfl⟩ | ⟨r, hr, _⟩)
    · exact ⟨a, by cases x <;> cases (run_liftExcept _ _).1 ha; rfl, h⟩
    · exact absurd rfl (hne st)
    · exact nomatch (run_liftExcept _ _).1 hr
  · rintro ⟨a, rfl, h⟩
    exact .inl ⟨a, (run_liftExcept _ _).2 rfl, h⟩

/-- A path of a lifted computation of the set monad, then `g`, goes on
from one of its results, or ends where it hits UB. -/
theorem run_lift_bind {s : SetM α} {g : α → ExceptT Stuck SetM β} {e : Ev (Except Stuck β)} :
    (ExceptT.lift s >>= g).run e ↔
      (∃ a, s (.ok a) ∧ (g a).run e) ∨ (∃ r, s (.ub r) ∧ e = .ub r) := by
  rw [run_bind]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨st, hst, rfl⟩ | ⟨r, hr, rfl⟩)
    · rcases (run_lift _ _).1 ha with ⟨a', h', he⟩ | ⟨_, _, he⟩
      · cases he; exact .inl ⟨a, h', h⟩
      · cases he
    · rcases (run_lift _ _).1 hst with ⟨_, _, he⟩ | ⟨_, _, he⟩ <;> cases he
    · rcases (run_lift _ _).1 hr with ⟨_, _, he⟩ | ⟨r', h', he⟩
      · cases he
      · cases he; exact .inr ⟨r, h', rfl⟩
  · rintro (⟨a, ha, h⟩ | ⟨r, hr, rfl⟩)
    · exact .inl ⟨a, (run_lift _ _).2 (.inl ⟨a, ha, rfl⟩), h⟩
    · exact .inr (.inr ⟨r, (run_lift _ _).2 (.inr ⟨r, hr, rfl⟩), rfl⟩)

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
  | callUB {args : HVector toType (sig o.op)} {s : Name} {g : Func d} {body genv} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some s → M.func? s = some g →
      g.enter args.toDVals = .ok (body, genv) →
      (Func.runOps (m := SetM) M n g genv body).run (.ub r) → Func.StepPath M n f env o os (.ub r)
  | callExh {args : HVector toType (sig o.op)} {s : Name} {g : Func d} {body genv} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some s → M.func? s = some g →
      g.enter args.toDVals = .ok (body, genv) →
      (Func.runOps (m := SetM) M n g genv body).run (.ok (.ok .fuelExhausted)) →
      Func.StepPath M n f env o os (.ok (.ok .fuelExhausted))
  | callRet {args : HVector toType (sig o.op)} {s : Name} {g : Func d} {body genv}
      {vs : List (DVal d)} {k : Nat} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some s → M.func? s = some g →
      g.enter args.toDVals = .ok (body, genv) →
      (Func.runOps (m := SetM) M n g genv body).run (.ok (.ok (.ret (vs, k)))) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      (Func.runOps (m := SetM) M (min k n) f ((o.results.map (·.1)).zip vs ++ env) os).run e →
      Func.StepPath M n f env o os e

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
              exact .callExh hreg' hargs hT' hc hg hen hr
            | .ret (vs, k), hr, h =>
              dsimp only at h
              split at h
              · obtain ⟨env₁, hb, h⟩ := (run_liftExcept_bind hne).1 h
                simp only [Env.bind] at hb
                split at hb
                · cases hb
                  exact .callRet hreg' hargs hT' hc hg hen hr (by assumption) (by assumption) h
                · cases hb
              · exact absurd ((run_liftExcept _ _).1 h) (hne _)
          · exact absurd rfl (hne st)
          · exact .callUB hreg' hargs hT' hc hg hen hu
        · exact absurd ((run_liftExcept _ _).1 h) (hne _)
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
      simp only [hc, hg]
      exact (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inr (.inr ⟨_, hx, rfl⟩))⟩
    | callExh hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      exact (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inl ⟨_, hx, rfl⟩)⟩
    | callRet hreg hargs hT hc hg hen hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      refine (run_liftExcept_bind hne).2 ⟨_, hen, (run_bind _ _ _).2 (.inl ⟨_, hx, ?_⟩)⟩
      dsimp only
      rw [ite_eq_left hty]
      exact (run_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩

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

/-- A run that runs out of fuel with `j` more steps runs out of fuel with
fewer: it takes the same path, and runs out sooner. -/
theorem Func.runOps_exhausted_down (M : Module d) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)),
      (Func.runOps (m := SetM) M (n + j) f env os).run (.ok (.ok .fuelExhausted)) →
      (Func.runOps (m := SetM) M n f env os).run (.ok (.ok .fuelExhausted)) := by
  have hne : Ev.NotStuck
      (.ok (.ok .fuelExhausted) : Ev (Except Stuck (Result (List (DVal d) × Nat)))) :=
    fun _ h => nomatch h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os h
    match n, os with
    | 0, _ => exact Func.run_runOps_zero.2 rfl
    | k + 1, [] => rw [Nat.add_right_comm] at h; exact absurd h (Func.run_runOps_nil hne)
    | k + 1, o :: os =>
      rw [Nat.add_right_comm] at h
      refine (Func.stepPath_iff hne).2 ?_
      cases (Func.stepPath_iff hne).1 h with
      | goto hreg hargs hT hos hx hj h =>
        exact .goto hreg hargs hT hos hx hj (ih k (Nat.lt_succ_self k) j _ _ _ h)
      | denote hreg hargs hT hc hx hlen h =>
        exact .denote hreg hargs hT hc hx hlen (ih k (Nat.lt_succ_self k) j _ _ _ h)
      | callExh hreg hargs hT hc hg hen hx =>
        exact .callExh hreg hargs hT hc hg hen (ih k (Nat.lt_succ_self k) j _ _ _ hx)
      | callRet hreg hargs hT hc hg hen hx hty hlen h =>
        rename_i vs kk
        rcases (Func.runOps_ahead M k j _ _ _).down_ret _ kk hx with ⟨hj, hx'⟩ | hx'
        · have hle : kk - j ≤ k := by
            have := Func.runOps_left_le M (k + j) _ _ _ _ _ hx
            omega
          have hmin : min kk (k + j) = (kk - j) + j := by
            have := Func.runOps_left_le M (k + j) _ _ _ _ _ hx
            omega
          rw [hmin] at h
          have h' := ih (kk - j) (Nat.lt_succ_of_le hle) j _ _ _ h
          refine .callRet hreg hargs hT hc hg hen hx' hty hlen ?_
          rwa [Nat.min_eq_left hle]
        · exact .callExh hreg hargs hT hc hg hen hx'

end Fir
