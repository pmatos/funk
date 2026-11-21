import Fir.Execution.TracePaths

/-!
# A traced run of ops, one step at a time

The refinement proofs over traced runs compare two runs path by path, as the
proofs with memory do (`Fir.Execution.MemoryStepPaths`). This section says,
once, every way in which a path of a run of ops in the traced layer goes on
from its first op, from a given traced state:

* A path that does not end stuck, with fuel left and an op to run, takes
  one of eight ways. A terminator's exit or an op's rule ends from the
  traced state, in UB after the acts it showed, or with the acts it showed
  and the traced state after it, from which the run goes on, after those
  acts. A call runs its callee in a frame: from the traced state with a new
  frame entered, and each return leaves the frame. When the callee returns,
  the caller goes on, with the steps that the callee leaves, from the
  traced state that the callee's return ends with, after the acts the
  callee showed.
* A run with no fuel runs out of fuel, and a block with no op left is
  stuck.
-/

namespace Fir

open Memory

variable {B α ε : Type}

/-! # The ways a step goes on -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A run in a call's frame, in the traced layer, runs from the traced state
with a new frame entered, and leaves the frame on each path that does not hit
UB. -/
theorem TraceM.run_inFrame (x : ExceptT ε (TraceM B (TraceState Mem unit)) α)
    (s : TraceState Mem unit) (e : TraceEnd B (TraceState Mem unit) (Except ε α)) :
    (inFrame x).run s e ↔ ∃ e', x.run { s with mem := s.mem.enter } e' ∧
      e = e'.map fun r => (r.1, r.2.1, { r.2.2 with mem := r.2.2.mem.exit }) :=
  Iff.rfl

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))]

variable (B) in
/-- The run of ops in the traced layer, from the traced state `s`. -/
abbrev Func.traceOps (M : Module d) (n : Nat) (f : Func d) (env : Env d) (os : List (Operation d))
    (s : TraceState Mem unit) :
    Paths (TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) :=
  (Func.runOps (m := TraceM B (TraceState Mem unit)) M n f env os).run s

variable (B) in
/-- The run of a callee's ops in a call's frame in the traced layer, from the
traced state `s`. -/
abbrev Func.traceCall (M : Module d) (n : Nat) (g : Func d) (genv : Env d)
    (body : List (Operation d)) (s : TraceState Mem unit) :
    Paths (TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) :=
  (inFrame (Func.runOps (m := TraceM B (TraceState Mem unit)) M n g genv body)).run s

/-- The ways a path of a traced run of the ops `o :: os` of `f`, with `n + 1`
steps, from the traced state `s`, goes on, when it does not end stuck. -/
inductive Func.TStepPath (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (s : TraceState Mem unit) :
    TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat))) → Prop
  | exitUB {args : HVector toType (sig o.op)} {r : String} {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM B (TraceState Mem unit)) o.op args s (.error (r, t)) →
      Func.TStepPath M n f env o os s (.error (r, t))
  | ret {args : HVector toType (sig o.op)} {t : List B} {s' : TraceState Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM B (TraceState Mem unit)) o.op args s (.ok (.ret, t, s')) →
      sig o.op = f.results →
      Func.TStepPath M n f env o os s (.ok (.ok (.ret (args.toDVals, n)), t, s'))
  | goto {args : HVector toType (sig o.op)} {i : Nat} {t : List B} {s' : TraceState Mem unit}
      {b : Block d} {env₁ : Env d} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM B (TraceState Mem unit)) o.op args s (.ok (.goto i, t, s')) →
      f.jump env o.succs i = .ok (b, env₁) → Func.traceOps B M n f env₁ b.body s' e →
      Func.TStepPath M n f env o os s (e.after t)
  | denoteUB {args : HVector toType (sig o.op)} {r : String} {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := TraceM B (TraceState Mem unit)) o.op args s (.error (r, t)) →
      Func.TStepPath M n f env o os s (.error (r, t))
  | denote {args : HVector toType (sig o.op)} {rs : HVector toType (returnTypes o.op)} {t : List B}
      {s' : TraceState Mem unit} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := TraceM B (TraceState Mem unit)) o.op args s (.ok (rs, t, s')) →
      (o.results.map (·.1)).length = rs.toDVals.length →
      Func.traceOps B M n f ((o.results.map (·.1)).zip rs.toDVals ++ env) os s' e →
      Func.TStepPath M n f env o os s (e.after t)
  | callUB {args : HVector toType (sig o.op)} {sym : Name} {g : Func d} {body genv} {r : String}
      {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some sym → M.func? sym = some g →
      g.enter args.toDVals = .ok (body, genv) → Func.traceCall B M n g genv body s (.error (r, t)) →
      Func.TStepPath M n f env o os s (.error (r, t))
  | callExh {args : HVector toType (sig o.op)} {sym : Name} {g : Func d} {body genv} {t : List B}
      {s' : TraceState Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some sym → M.func? sym = some g →
      g.enter args.toDVals = .ok (body, genv) →
      Func.traceCall B M n g genv body s (.ok (.ok .fuelExhausted, t, s')) →
      Func.TStepPath M n f env o os s (.ok (.ok .fuelExhausted, t, s'))
  | callRet {args : HVector toType (sig o.op)} {sym : Name} {g : Func d} {body genv}
      {vs : List (DVal d)} {k : Nat} {t : List B} {s' : TraceState Mem unit} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some sym → M.func? sym = some g →
      g.enter args.toDVals = .ok (body, genv) →
      Func.traceCall B M n g genv body s (.ok (.ok (.ret (vs, k)), t, s')) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      Func.traceOps B M (min k n) f ((o.results.map (·.1)).zip vs ++ env) os s' e →
      Func.TStepPath M n f env o os s (e.after t)

/-- A path of a traced run of ops that is not stuck, from `s`, is a path that
the first op goes on by, and every such path is a path of the run. -/
theorem Func.tStepPath_iff {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {o : Operation d} {os : List (Operation d)} {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (hne : TraceEnd.NotStuck e) :
    Func.traceOps B M (n + 1) f env (o :: os) s e ↔ Func.TStepPath M n f env o os s e := by
  constructor
  · intro h
    simp only [Func.traceOps, Func.runOps] at h
    split at h
    · obtain ⟨_, h, _⟩ := (TraceM.run_liftExcept_bind hne).1 h
      cases h
    rename_i hreg
    have hreg' : o.ownsCoreRegion = false := by simpa using hreg
    obtain ⟨args, hargs, h⟩ := (TraceM.run_liftExcept_bind hne).1 h
    split at h
    · rename_i hT
      split at h
      · obtain ⟨_, h, _⟩ := (TraceM.run_liftExcept_bind hne).1 h
        cases h
      rename_i hos
      have hos' : os = [] := by simpa using hos
      rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨x, t, s', e', hx, h, he⟩ | ⟨r, t, hr, he⟩ <;>
        rw [he]
      · cases x with
        | ret =>
          dsimp only at h
          split at h
          · have h : e' = _ := h
            subst h
            simp only [TraceEnd.after, List.append_nil]
            exact .ret hreg' hargs hT hos' hx (by assumption)
          · exact absurd h (TraceM.run_stuck (he ▸ hne).of_after)
        | goto i =>
          dsimp only at h
          obtain ⟨⟨b, env₁⟩, hj, h⟩ :=
            (TraceM.run_liftExcept_bind (he ▸ hne).of_after).1 h
          exact .goto hreg' hargs hT hos' hx hj h
      · exact .exitUB hreg' hargs hT hos' hr
    · rename_i hT
      have hT' : isTerminator o.op = false := by simpa using hT
      split at h
      · rename_i hc
        rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨rs, t, s', e', hrs, h, he⟩ | ⟨r, t, hr, he⟩ <;>
          rw [he]
        · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind (he ▸ hne).of_after).1 h
          simp only [Env.bind] at hb
          split at hb
          · cases hb
            exact .denote hreg' hargs hT' hc hrs (by assumption) h
          · cases hb
        · exact .denoteUB hreg' hargs hT' hc hr
      · rename_i sym hc
        split at h
        · rename_i g hg
          obtain ⟨⟨body, genv⟩, hen, h⟩ := (TraceM.run_liftExcept_bind hne).1 h
          rcases (TraceM.run_except_bind _ _ _ _).1 h with
            ⟨x, t, s', e', hx, h, he⟩ | ⟨st, t, s', _, he⟩ | ⟨r, t, hr, he⟩ <;> rw [he]
          · have hne' := TraceEnd.NotStuck.of_after (he ▸ hne)
            rcases x with ⟨vs, k⟩ | _
            · dsimp only at h
              split at h
              · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind hne').1 h
                simp only [Env.bind] at hb
                split at hb
                · cases hb
                  exact .callRet hreg' hargs hT' hc hg hen hx (by assumption) (by assumption) h
                · cases hb
              · exact absurd h (TraceM.run_stuck hne')
            · have h : e' = _ := h
              subst h
              simp only [TraceEnd.after, List.append_nil]
              exact .callExh hreg' hargs hT' hc hg hen hx
          · exact absurd he (hne st t s')
          · exact .callUB hreg' hargs hT' hc hg hen hr
        · exact absurd h (TraceM.run_stuck hne)
  · intro h
    simp only [Func.traceOps, Func.runOps]
    cases h with
    | exitUB hreg hargs hT hos hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
    | ret hreg hargs hT hos hx hs =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx,
        by dsimp only; rw [ite_eq_left hs]; rfl, by simp [TraceEnd.after]⟩)
    | goto hreg hargs hT hos hx hj h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx,
        (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2 ⟨_, hj, h⟩, rfl⟩)
    | denoteUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
    | denote hreg hargs hT hc hx hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx,
        (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2
          ⟨_, Env.bind_ok _ _ hlen, h⟩, rfl⟩)
    | callUB hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      exact (TraceM.run_liftExcept_bind hne).2 ⟨_, hen,
        (TraceM.run_except_bind _ _ _ _).2 (.inr (.inr ⟨_, _, hx, rfl⟩))⟩
    | callExh hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      exact (TraceM.run_liftExcept_bind hne).2 ⟨_, hen,
        (TraceM.run_except_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, rfl, by simp [TraceEnd.after]⟩)⟩
    | callRet hreg hargs hT hc hg hen hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hen,
        (TraceM.run_except_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, ?_, rfl⟩)⟩
      dsimp only
      rw [ite_eq_left hty]
      exact (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2
        ⟨_, Env.bind_ok _ _ hlen, h⟩

/-- A traced run with no fuel runs out of fuel, showing nothing, and only
so. -/
theorem Func.traceOps_zero {M : Module d} {f : Func d} {env : Env d} {os : List (Operation d)}
    {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))} :
    Func.traceOps B M 0 f env os s e ↔ e = .ok (.ok .fuelExhausted, [], s) := by
  simp only [Func.traceOps, Func.runOps]
  exact Iff.rfl

/-- A block with no op left is stuck, from any traced state. -/
theorem Func.traceOps_nil {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (hne : TraceEnd.NotStuck e) : ¬ Func.traceOps B M (n + 1) f env [] s e := by
  simp only [Func.traceOps, Func.runOps]
  exact TraceM.run_stuck hne

end Fir
