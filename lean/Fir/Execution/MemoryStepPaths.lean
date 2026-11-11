import Fir.Execution.MemoryMonotone
import Fir.Execution.RunPaths

/-!
# A run of ops with memory, one step at a time

The refinement proofs compare two runs path by path: they follow each path
of one run, and find a path of the other that allows it (the section on a
run of ops, one step at a time). This section says, once, every way in
which a path of a run of ops with memory goes on from its first op, read
from given memories (the section on how a run with memory ends):

* A path that does not end stuck, with fuel left and an op to run, takes
  one of the eight ways of a run in the set monad, each from the memories
  that the run starts from. A terminator's exit or an op's rule ends from
  them, in UB or with the memories after it, from which the run goes on. A
  call runs its callee in a frame: from them with a new frame entered, and
  each return leaves the frame. When the callee returns, the caller goes
  on, with the steps that the callee leaves, from the memories that the
  callee's return ends with.
* A run with no fuel runs out of fuel, and a block with no op left is
  stuck.
-/

namespace Fir

open SetM Memory

variable {σ α β : Type}

/-! # Paths from given memories -/

/-- A path of a check, then `g`, that is not stuck goes on from the value
that the check holds, from the same memories. -/
theorem runFrom_liftExcept_bind {x : Except Stuck β}
    {g : β → ExceptT Stuck (StateT σ SetM) (Result (α × Nat))} {S : σ}
    {e : Ev (Except Stuck (Result ((α × σ) × Nat)))} (hne : Ev.NotStuck e) :
    (runFrom (liftExcept x >>= g) S).run e ↔ ∃ b, x = .ok b ∧ (runFrom (g b) S).run e := by
  rw [runFrom_bind, fromState_liftExcept, run_liftExcept_bind hne]
  constructor
  · rintro ⟨p, hp, h⟩
    cases x with
    | ok b => cases hp; exact ⟨b, rfl, h⟩
    | error _ => cases hp
  · rintro ⟨b, rfl, h⟩
    exact ⟨(b, S), rfl, h⟩

/-- A path of a computation of the layer, then `g`, goes on from one of its
results with the memories it ends with, or ends where it hits UB. -/
theorem runFrom_lift_bind {c : StateT σ SetM β}
    {g : β → ExceptT Stuck (StateT σ SetM) (Result (α × Nat))} {S : σ}
    {e : Ev (Except Stuck (Result ((α × σ) × Nat)))} :
    (runFrom (ExceptT.lift c >>= g) S).run e ↔
      (∃ b S', c S (.ok (b, S')) ∧ (runFrom (g b) S').run e) ∨ (∃ r, c S (.ub r) ∧ e = .ub r) := by
  rw [runFrom_bind, fromState_lift, run_lift_bind]
  constructor
  · rintro (⟨p, hp, h⟩ | h)
    · exact .inl ⟨p.1, p.2, hp, h⟩
    · exact .inr h
  · rintro (⟨b, S', hp, h⟩ | h)
    · exact .inl ⟨(b, S'), hp, h⟩
    · exact .inr h

/-- A run of ops ends with a return, from `S`, exactly when it ends so read
from `S` with its memories. -/
theorem runFrom_ret_iff {x : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))} {S S' : σ} {a : α}
    {k : Nat} :
    (runFrom x S).run (.ok (.ok (.ret ((a, S'), k)))) ↔
      (fromState x S).run (.ok (.ok (.ret (a, k), S'))) := by
  unfold runFrom
  rw [SetM.run_map]
  constructor
  · rintro (⟨⟨r, S''⟩, h, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩)
    · cases r with
      | ret p => cases he; exact h
      | fuelExhausted => cases he
    · cases he
    · cases he
  · exact fun h => .inl ⟨_, h, rfl⟩

/-- A run of ops runs out of fuel, from `S`, exactly when it does so read
from `S` with some memories. -/
theorem runFrom_exh_iff {x : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))} {S : σ} :
    (runFrom x S).run (.ok (.ok .fuelExhausted)) ↔
      ∃ S', (fromState x S).run (.ok (.ok (.fuelExhausted, S'))) := by
  unfold runFrom
  rw [SetM.run_map]
  constructor
  · rintro (⟨⟨r, S''⟩, h, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩)
    · cases r with
      | ret p => cases he
      | fuelExhausted => exact ⟨S'', h⟩
    · cases he
    · cases he
  · rintro ⟨S', h⟩
    exact .inl ⟨_, h, rfl⟩

/-- A run of ops hits UB, from `S`, exactly when it does so read from `S`
with its memories. -/
theorem runFrom_ub_iff {x : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))} {S : σ} {r : String} :
    (runFrom x S).run (.ub r) ↔ (fromState x S).run (.ub r) := by
  unfold runFrom
  rw [SetM.run_map]
  constructor
  · rintro (⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, h, he⟩)
    · cases he
    · cases he
    · cases he; exact h
  · exact fun h => .inr (.inr ⟨_, h, rfl⟩)

/-- A path of a run of ops, then `K`, that is not stuck, from `S`, goes on
by `K` from a return of the run with the memories it ends with, or ends
where the run runs out of fuel or hits UB, when `K` runs out of fuel on a
run that does. -/
theorem runFrom_bindRun {x : ExceptT Stuck (StateT σ SetM) (Result (β × Nat))}
    {K : Result (β × Nat) → ExceptT Stuck (StateT σ SetM) (Result (α × Nat))}
    (hK : K .fuelExhausted = pure .fuelExhausted) {S : σ}
    {e : Ev (Except Stuck (Result ((α × σ) × Nat)))} (hne : Ev.NotStuck e) :
    (runFrom (x >>= K) S).run e ↔
      (∃ b T k, (runFrom x S).run (.ok (.ok (.ret ((b, T), k)))) ∧
        (runFrom (K (.ret (b, k))) T).run e) ∨
      ((runFrom x S).run (.ok (.ok .fuelExhausted)) ∧ e = .ok (.ok .fuelExhausted)) ∨
      (∃ r, (runFrom x S).run (.ub r) ∧ e = .ub r) := by
  rw [runFrom_bind, run_bind]
  constructor
  · rintro (⟨⟨r, T⟩, hp, h⟩ | ⟨st, _, rfl⟩ | ⟨r, hr, rfl⟩)
    · cases r with
      | ret p => exact .inl ⟨p.1, T, p.2, runFrom_ret_iff.2 hp, h⟩
      | fuelExhausted =>
        dsimp only at h
        rw [hK, runFrom_exhausted] at h
        exact .inr (.inl ⟨runFrom_exh_iff.2 ⟨T, hp⟩, (run_pure _ _).1 h⟩)
    · exact absurd rfl (hne st)
    · exact .inr (.inr ⟨r, runFrom_ub_iff.2 hr, rfl⟩)
  · rintro (⟨b, T, k, hx, h⟩ | ⟨hx, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact .inl ⟨(.ret (b, k), T), runFrom_ret_iff.1 hx, h⟩
    · obtain ⟨T, hx⟩ := runFrom_exh_iff.1 hx
      refine .inl ⟨(.fuelExhausted, T), hx, ?_⟩
      dsimp only
      rw [hK, runFrom_exhausted]
      exact (run_pure _ _).2 rfl
    · exact .inr (.inr ⟨r, runFrom_ub_iff.1 hr, rfl⟩)

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-! # The ways a step goes on -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-- The run of ops with memory, from `S`, read in the set monad. -/
abbrev Func.memOps (M : Module d) (n : Nat) (f : Func d) (env : Env d) (os : List (Operation d))
    (S : Memories Mem unit) :
    ExceptT Stuck SetM (Result ((List (DVal d) × Memories Mem unit) × Nat)) :=
  runFrom (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env os) S

/-- The run with memory of a callee's ops in a call's frame, from `S`, read
in the set monad: they run from `S` with a new frame entered, and each
return leaves the frame. -/
abbrev Func.memCall (M : Module d) (n : Nat) (g : Func d) (genv : Env d)
    (body : List (Operation d)) (S : Memories Mem unit) :
    ExceptT Stuck SetM (Result ((List (DVal d) × Memories Mem unit) × Nat)) :=
  runFrom (inFrame (Func.runOps (m := StateT (Memories Mem unit) SetM) M n g genv body)) S

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
  | callUB {args : HVector toType (sig o.op)} {s : Name} {g : Func d} {body genv} {r : String} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some s → M.func? s = some g →
      g.enter args.toDVals = .ok (body, genv) →
      (Func.memCall M n g genv body S).run (.ub r) → Func.MemStepPath M n f env o os S (.ub r)
  | callExh {args : HVector toType (sig o.op)} {s : Name} {g : Func d} {body genv} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some s → M.func? s = some g →
      g.enter args.toDVals = .ok (body, genv) →
      (Func.memCall M n g genv body S).run (.ok (.ok .fuelExhausted)) →
      Func.MemStepPath M n f env o os S (.ok (.ok .fuelExhausted))
  | callRet {args : HVector toType (sig o.op)} {s : Name} {g : Func d} {body genv}
      {vs : List (DVal d)} {S' : Memories Mem unit} {k : Nat} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some s → M.func? s = some g →
      g.enter args.toDVals = .ok (body, genv) →
      (Func.memCall M n g genv body S).run (.ok (.ok (.ret ((vs, S'), k)))) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      (Func.memOps M (min k n) f ((o.results.map (·.1)).zip vs ++ env) os S').run e →
      Func.MemStepPath M n f env o os S e

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
                exact .callRet hreg' hargs hT' hc hg hen hr (by assumption) (by assumption) h
              · cases hb
            · rw [runFrom_stuck] at h
              exact absurd ((run_liftExcept _ _).1 h) (hne _)
          · exact .callExh hreg' hargs hT' hc hg hen hr
          · exact .callUB hreg' hargs hT' hc hg hen hu
        · rw [runFrom_stuck] at h
          exact absurd ((run_liftExcept _ _).1 h) (hne _)
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
      simp only [hc, hg]
      exact (runFrom_liftExcept_bind hne).2 ⟨_, hen,
        (runFrom_bindRun (by rfl) hne).2 (.inr (.inr ⟨_, hx, rfl⟩))⟩
    | callExh hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      exact (runFrom_liftExcept_bind hne).2 ⟨_, hen,
        (runFrom_bindRun (by rfl) hne).2 (.inr (.inl ⟨hx, rfl⟩))⟩
    | callRet hreg hargs hT hc hg hen hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc, hg]
      refine (runFrom_liftExcept_bind hne).2 ⟨_, hen,
        (runFrom_bindRun (by rfl) hne).2 (.inl ⟨_, _, _, hx, ?_⟩)⟩
      dsimp only
      rw [ite_eq_left hty]
      exact (runFrom_liftExcept_bind hne).2 ⟨_, Env.bind_ok _ _ hlen, h⟩

/-- A run with memory with no fuel runs out of fuel, and only so. -/
theorem Func.run_memOps_zero {M : Module d} {f : Func d} {env : Env d} {os : List (Operation d)}
    {S : Memories Mem unit} {e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))} :
    (Func.memOps M 0 f env os S).run e ↔ e = .ok (.ok .fuelExhausted) := by
  simp only [Func.memOps, Func.runOps, runFrom_exhausted]; exact run_pure _ _

/-- A block with no op left is stuck, from any memories. -/
theorem Func.run_memOps_nil {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {S : Memories Mem unit} {e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (hne : Ev.NotStuck e) : ¬ (Func.memOps M (n + 1) f env [] S).run e := by
  simp only [Func.memOps, Func.runOps, runFrom_stuck]
  exact fun h => hne _ ((run_liftExcept _ _).1 h)

end Fir
