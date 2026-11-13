import Fir.Execution.StatePaths
import Fir.Execution.MemoryRuns

/-!
# Runs with memory at every budget

The runs with memory of every function of every module of every dialect
are fuel-monotone, whatever its ops do to the memories. The proof is the
proof for runs in the set monad (the section on runs at every budget), read
from given memories (the section on how a run with memory ends): the
interpreter alone counts the fuel, and an op never sees it, nor does the
memory effect or a frame. So the two facts it rests on hold from any
memories, each proved by induction on the budget:

* _A run gives back at most the fuel it was given._
* _A run with more steps of fuel is ahead by as many steps._ From the same
  memories, each of its returns is a return of the smaller run that leaves
  that many fewer steps and ends with the same memories, or the smaller
  run can run out of fuel; each of the smaller run's returns, with its
  memories, is one of the larger run's that leaves that many more steps;
  and the two hit the same UB.

A step of a run goes on from the memories that the step before it ended
with, and both runs take the same steps until one runs out of fuel, so the
two reach each step from the same memories. A call runs its callee from the
memories with a new frame entered, the same in both runs, and leaves the
frame on each path that returns, so the caller goes on from the same
memories in both, with as many more steps.
-/

namespace Fir

open SetM Memory

variable {σ α β γ : Type}

/-! # Mapping what a run returns -/

/-- The run's return with its value mapped by `F`, and the same steps
left. -/
def Result.mapVal (F : α → β) : Result (α × Nat) → Result (β × Nat)
  | .ret (a, k) => .ret (F a, k)
  | .fuelExhausted => .fuelExhausted

/-- A path of `f <$> s` ends with `f` of a result of `s`, or where `s` ends
with an error or with UB. -/
theorem SetM.run_map {ε : Type} (f : α → β) (s : ExceptT ε SetM α) (e : Ev (Except ε β)) :
    (f <$> s).run e ↔ (∃ a, s.run (.ok (.ok a)) ∧ e = .ok (.ok (f a))) ∨
      (∃ er, s.run (.ok (.error er)) ∧ e = .ok (.error er)) ∨ (∃ r, s.run (.ub r) ∧ e = .ub r) := by
  rw [map_eq_pure_bind, run_bind]
  constructor
  · rintro (⟨a, ha, he⟩ | h | h)
    · exact .inl ⟨a, ha, (run_pure _ _).1 he⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (⟨a, ha, rfl⟩ | h | h)
    · exact .inl ⟨a, ha, rfl⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)

/-- Mapping what a run returns keeps the steps it leaves. -/
theorem LeavesAtMost.mapVal {n : Nat} (F : α → β) {s : ExceptT Stuck SetM (Result (α × Nat))}
    (h : LeavesAtMost n s) : LeavesAtMost n (Result.mapVal F <$> s) := by
  intro a k hk
  rcases (SetM.run_map _ s _).1 hk with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · match r, hr, he with
    | .ret (a', k'), hr, he => cases he; exact h a' k hr
    | .fuelExhausted, _, he => cases he
  · cases he
  · cases he

/-- Mapping what two runs return keeps one ahead of the other. -/
theorem Ahead.mapVal {j : Nat} (F : α → β) {s t : ExceptT Stuck SetM (Result (α × Nat))}
    (h : Ahead j s t) : Ahead j (Result.mapVal F <$> s) (Result.mapVal F <$> t) where
  up_ret a k hs := by
    rcases (SetM.run_map _ s _).1 hs with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · match r, hr, he with
      | .ret (a', k'), hr, he =>
        cases he
        exact (SetM.run_map _ t _).2 (.inl ⟨_, h.up_ret a' k hr, rfl⟩)
      | .fuelExhausted, _, he => cases he
    · cases he
    · cases he
  up_ub r hs := by
    rcases (SetM.run_map _ s _).1 hs with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
    · cases he
      exact (SetM.run_map _ t _).2 (.inr (.inr ⟨_, h.up_ub _ hr, rfl⟩))
  down_ret a k ht := by
    rcases (SetM.run_map _ t _).1 ht with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · match r, hr, he with
      | .ret (a', k'), hr, he =>
        cases he
        rcases h.down_ret a' k hr with ⟨hj, hs⟩ | hs
        · exact .inl ⟨hj, (SetM.run_map _ s _).2 (.inl ⟨_, hs, rfl⟩)⟩
        · exact .inr ((SetM.run_map _ s _).2 (.inl ⟨_, hs, rfl⟩))
      | .fuelExhausted, _, he => cases he
    · cases he
    · cases he
  down_ub r ht := by
    rcases (SetM.run_map _ t _).1 ht with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨r', hr, he⟩
    · cases he
    · cases he
    · cases he
      rcases h.down_ub _ hr with hs | hs
      · exact .inl ((SetM.run_map _ s _).2 (.inr (.inr ⟨_, hs, rfl⟩)))
      · exact .inr ((SetM.run_map _ s _).2 (.inl ⟨_, hs, rfl⟩))

/-! # A call, from given memories -/

/-- A sequence whose first computation is a run of ops: what follows sees
its return with the memories it ended with, and a run out of fuel stops it,
when what follows is out of fuel on such a run. -/
theorem fromState_bind_result {x : ExceptT Stuck (StateT σ SetM) (Result (β × Nat))}
    {K : Result (β × Nat) × σ → ExceptT Stuck SetM (Result (γ × Nat))}
    (hK : ∀ S', K (.fuelExhausted, S') = pure .fuelExhausted) (S : σ) :
    (fromState x S >>= K) =
      runFrom x S >>= fun r => match r with
        | .ret ((b, S'), k) => K (.ret (b, k), S')
        | .fuelExhausted => pure .fuelExhausted := by
  simp only [runFrom, bind_map_left]
  refine congrArg (fromState x S >>= ·) (funext fun p => ?_)
  obtain ⟨r, S'⟩ := p
  cases r with
  | ret p => rfl
  | fuelExhausted => exact hK S'

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A run of ops in a call's frame, from `S`, runs from `S` with a new frame
entered, and leaves the frame on each return. -/
theorem runFrom_inFrame (x : ExceptT Stuck (StateT (Memories Mem unit) SetM) (Result (α × Nat)))
    (S : Memories Mem unit) :
    runFrom (inFrame x) S = Result.mapVal (fun p : α × Memories Mem unit => (p.1, p.2.exit)) <$>
      runFrom x S.enter := by
  simp only [runFrom, fromState_inFrame, Functor.map_map]
  refine congrArg (· <$> fromState x S.enter) (funext fun p => ?_)
  obtain ⟨r, S'⟩ := p
  cases r <;> rfl

/-- A call, then what its caller does with the result, from the same
memories: when the callee with more fuel is ahead of it from any memories,
and so is what the caller does with a return that leaves `j` more steps,
from the memories it ends with, so is the whole. A callee that runs out of
fuel ends its caller so. -/
theorem Ahead.bindCall {j n : Nat}
    {x y : ExceptT Stuck (StateT (Memories Mem unit) SetM) (Result (β × Nat))}
    {K L : Result (β × Nat) × Memories Mem unit → ExceptT Stuck SetM (Result (γ × Nat))}
    (hxy : ∀ S, Ahead j (runFrom x S) (runFrom y S)) (hx : ∀ S, LeavesAtMost n (runFrom x S))
    (hK : ∀ S', K (.fuelExhausted, S') = pure .fuelExhausted)
    (hL : ∀ S', L (.fuelExhausted, S') = pure .fuelExhausted)
    (hKL : ∀ b k S', k ≤ n → Ahead j (K (.ret (b, k), S')) (L (.ret (b, k + j), S')))
    (S : Memories Mem unit) :
    Ahead j (fromState (inFrame x) S >>= K) (fromState (inFrame y) S >>= L) := by
  rw [fromState_bind_result hK, fromState_bind_result hL, runFrom_inFrame, runFrom_inFrame]
  refine Ahead.bindRun ((hxy S.enter).mapVal _) ((hx S.enter).mapVal _) rfl rfl ?_
  intro ⟨b, S'⟩ k hk
  exact hKL b k S' hk

/-! # Runs of ops with memory -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-- A run of ops with memory gives back at most the steps of fuel it was
given, from any memories. -/
theorem Func.runOps_memLeft_le (M : Module d) (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)) (S : Memories Mem unit),
      LeavesAtMost n
        (runFrom (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env os) S) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os S
    match n, os with
    | 0, _ => simp only [Func.runOps, runFrom_exhausted]; exact LeavesAtMost.exhausted
    | _ + 1, [] => simp only [Func.runOps, runFrom_stuck]; exact LeavesAtMost.of_stuck
    | k + 1, o :: os =>
      simp only [Func.runOps]
      all_goals repeat' (first
        | (rw [runFrom_bind]; apply LeavesAtMost.bind; intro _ _)
        | split
        | (rw [runFrom_stuck]; exact LeavesAtMost.of_stuck)
        | (rw [runFrom_exhausted]; exact LeavesAtMost.exhausted)
        | (rw [runFrom_ret]; exact LeavesAtMost.ret (Nat.le_succ _))
        | exact (ih _ (Nat.lt_succ_self _) _ _ _ _).mono (Nat.le_succ _)
        | exact (ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _ _).mono
            (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_succ _)))

/-- A run of ops with memory with `j` more steps of fuel is ahead of the
run with fewer, from the same memories, calls included. -/
theorem Func.runOps_memAhead (M : Module d) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)) (S : Memories Mem unit),
      Ahead j (runFrom (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env os) S)
        (runFrom (Func.runOps (m := StateT (Memories Mem unit) SetM) M (n + j) f env os) S) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os S
    match n, os with
    | 0, _ => simp only [Func.runOps, runFrom_exhausted]; exact Ahead.exhausted
    | k + 1, [] =>
      rw [Nat.add_right_comm]
      simp only [Func.runOps, runFrom_stuck]
      exact Ahead.of_stuck
    | k + 1, o :: os =>
      rw [Nat.add_right_comm]
      simp only [Func.runOps]
      all_goals repeat' (first
        | exact ih _ (Nat.lt_succ_self _) _ _ _ _ _
        | (rw [Nat.min_eq_left hk, Nat.min_eq_left (Nat.add_le_add_right hk _)]
           exact ih _ (Nat.lt_succ_of_le hk) _ _ _ _ _)
        | (simp only [runFrom_stuck]; exact Ahead.of_stuck)
        | (simp only [runFrom_ret]; exact Ahead.ret)
        | (refine Ahead.bindCall (fun S => ih _ (Nat.lt_succ_self _) _ _ _ _ S)
            (fun S => Func.runOps_memLeft_le _ _ _ _ _ S) ?_ ?_ ?_ _
           · intro _; exact runFrom_exhausted _
           · intro _; exact runFrom_exhausted _
           intro _ _ _ hk
           dsimp only)
        | simp only [runFrom_bind]
        | split
        | (apply Ahead.bind; intro _ _))

/-! # The run of a function -/

/-- What a function does with the run of its entry block's ops: it returns
what they return, mapped by `g`, or runs out of fuel when they do. -/
def Result.finish (g : α → β) (X : ExceptT Stuck SetM (Result (α × Nat))) :
    ExceptT Stuck SetM (Result β) :=
  X >>= fun r => match r with
    | .ret (a, _) => pure (.ret (g a))
    | .fuelExhausted => pure .fuelExhausted

variable {j : Nat} {X Y : ExceptT Stuck SetM (Result (α × Nat))} (g : α → β)
  {e : Ev (Except Stuck (Result β))}

/-- A function whose ops with more fuel are ahead: each return or UB of the
smaller run is one of the larger. -/
theorem Ahead.finish_up (h : Ahead j X Y) (hne : e ≠ .ok (.ok .fuelExhausted))
    (hst : ∀ st, e ≠ .ok (.error st)) (hx : (Result.finish g X).run e) :
    (Result.finish g Y).run e := by
  rcases (run_bind _ _ _).1 hx with ⟨r, hr, hk⟩ | ⟨st, _, he⟩ | ⟨u, hu, he⟩
  · match r, hr, hk with
    | .ret (a, k), hr, hk =>
      exact (run_bind _ _ _).2 (.inl ⟨_, h.up_ret a k hr, hk⟩)
    | .fuelExhausted, _, hk => exact absurd ((run_pure _ _).1 hk) hne
  · exact absurd he (hst st)
  · exact (run_bind _ _ _).2 (.inr (.inr ⟨u, h.up_ub u hu, he⟩))

/-- A function whose ops with more fuel are ahead: each return or UB of the
larger run is one of the smaller, unless the smaller can run out of
fuel. -/
theorem Ahead.finish_down (h : Ahead j X Y) (hne : e ≠ .ok (.ok .fuelExhausted))
    (hst : ∀ st, e ≠ .ok (.error st)) (hy : (Result.finish g Y).run e) :
    (Result.finish g X).run e ∨ (Result.finish g X).run (.ok (.ok .fuelExhausted)) := by
  have exh : X.run (.ok (.ok .fuelExhausted)) →
      (Result.finish g X).run (.ok (.ok .fuelExhausted)) :=
    fun hx => (run_bind _ _ _).2 (.inl ⟨_, hx, rfl⟩)
  rcases (run_bind _ _ _).1 hy with ⟨r, hr, hk⟩ | ⟨st, _, he⟩ | ⟨u, hu, he⟩
  · match r, hr, hk with
    | .ret (a, k), hr, hk =>
      rcases h.down_ret a k hr with ⟨_, hx⟩ | hx
      · exact .inl ((run_bind _ _ _).2 (.inl ⟨_, hx, hk⟩))
      · exact .inr (exh hx)
    | .fuelExhausted, _, hk => exact absurd ((run_pure _ _).1 hk) hne
  · exact absurd he (hst st)
  · rcases h.down_ub u hu with hx | hx
    · exact .inl ((run_bind _ _ _).2 (.inr (.inr ⟨u, hx, he⟩)))
    · exact .inr (exh hx)

/-! # Runs with memory are fuel-monotone -/

omit [DecidableEq Mem] in
/-- The ways a computation of the layer may end from `S`, without the
memories it ends with. -/
theorem fromState_fst {ε : Type} (x : ExceptT ε (StateT σ SetM) α) (S : σ) :
    Prod.fst <$> x.run S = (Prod.fst <$> fromState x S).run := by
  simp only [fromState, ExceptT.run_map, ExceptT.run_mk, Functor.map_map]
  refine congrArg (· <$> x.run S) (funext fun p => ?_)
  obtain ⟨r, S'⟩ := p
  cases r <;> rfl

/-- A function that starts at its entry block's ops `body` in `env` runs
them in a frame, and returns the values they return. -/
theorem Func.run_of_enter (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (n : Nat)
    {body : List (Operation d)} {env : Env d} (hen : f.enter args.toDVals = .ok (body, env)) :
    f.run M (m := StateT (Memories Mem unit) SetM) args n =
      inFrame (Func.runOps M n f env body) >>= fun r => match r with
        | .ret (vs, _) => pure (.ret vs)
        | .fuelExhausted => pure .fuelExhausted := by
  simp only [Func.run, hen]
  exact pure_bind _ _

/-- A function that cannot start is stuck there, on every path of its run
from `S`. -/
theorem Func.fromState_run_stuck (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (n : Nat) (S : Memories Mem unit) {st : Stuck}
    (hen : f.enter args.toDVals = .error st)
    {e : Ev (Except Stuck (Result (List (DVal d)) × Memories Mem unit))}
    (h : (fromState (f.run M (m := StateT (Memories Mem unit) SetM) args n) S).run e) :
    e = .ok (.error st) := by
  simp only [Func.run, fromState_bind, hen, fromState_liftExcept] at h
  rcases (run_bind _ _ _).1 h with ⟨_, h, -⟩ | ⟨er, h, he⟩ | ⟨_, h, -⟩
  · cases (run_liftExcept _ _).1 h
  · cases (run_liftExcept _ _).1 h
    exact he
  · cases (run_liftExcept _ _).1 h

/-- The run of a function with memory, from `S`, without the memories it
ends with, when it starts: its entry block's ops, run from `S` with a frame
entered, finished. -/
theorem Func.run_fromState (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (n : Nat) (S : Memories Mem unit)
    {body : List (Operation d)} {env : Env d} (hen : f.enter args.toDVals = .ok (body, env)) :
    Prod.fst <$> fromState (f.run M (m := StateT (Memories Mem unit) SetM) args n) S =
      Result.finish Prod.fst (runFrom (Func.runOps M n f env body) S.enter) := by
  rw [Func.run_of_enter M f args n hen, fromState_bind, fromState_inFrame, bind_map_left, map_bind]
  simp only [Result.finish, runFrom, bind_map_left]
  refine congrArg (fromState _ S.enter >>= ·) (funext fun q => ?_)
  obtain ⟨r, S'⟩ := q
  cases r with
  | ret p => simp only [fromState_pure, map_pure]; rfl
  | fuelExhausted => simp only [fromState_pure, map_pure]; rfl

/-- A run of a function with memory that cannot start is stuck there, on
every path. -/
theorem Func.run_fromState_stuck (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (n : Nat) (S : Memories Mem unit) {st : Stuck}
    (hen : f.enter args.toDVals = .error st) (e : Ev (Except Stuck (Result (List (DVal d)))))
    (h : (Prod.fst <$> fromState (f.run M (m := StateT (Memories Mem unit) SetM) args n) S).run e) :
    e = .ok (.error st) := by
  have hx := fun {e'} => Func.fromState_run_stuck M f args n S hen (e := e')
  rcases (SetM.run_map _ _ _).1 h with ⟨_, h1, -⟩ | ⟨_, h1, rfl⟩ | ⟨_, h1, -⟩
  · cases hx h1
  · cases hx h1
    rfl
  · cases hx h1

end

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] {N : Type} [DecidableEq N]

/-- The runs with memory of every function of every module of every
dialect, wherever a run names its memories, are fuel-monotone, calls
included, whatever its ops do to the memories. -/
theorem Func.memRuns_fuelMonotone (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
    (M : Module d) (f : Func d) (args : HVector toType (f.params.map (·.2))) :
    FuelMonotone (f.memRuns lay ρ M args) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  have key : ∀ n, f.memRuns lay ρ M args n = (Prod.fst <$> fromState
      (f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args n) Memories.empty).run :=
    fun n => fromState_fst _ _
  have up : ∀ n j e, e ≠ .ok (.ok .fuelExhausted) → (∀ st, e ≠ .ok (.error st)) →
      f.memRuns lay ρ M args n e → f.memRuns lay ρ M args (n + j) e := by
    intro n j e hne hst hs
    rw [key] at hs ⊢
    cases hen : f.enter args.toDVals with
    | error st => exact absurd (Func.run_fromState_stuck M f args n _ hen _ hs) (hst st)
    | ok p =>
      obtain ⟨body, env⟩ := p
      rw [Func.run_fromState M f args n _ hen] at hs
      rw [Func.run_fromState M f args (n + j) _ hen]
      exact (Func.runOps_memAhead M n j f env body _).finish_up Prod.fst hne hst hs
  have down : ∀ n j e, e ≠ .ok (.ok .fuelExhausted) → (∀ st, e ≠ .ok (.error st)) →
      f.memRuns lay ρ M args (n + j) e →
      f.memRuns lay ρ M args n e ∨ f.memRuns lay ρ M args n (.ok (.ok .fuelExhausted)) := by
    intro n j e hne hst ht
    rw [key] at ht ⊢
    cases hen : f.enter args.toDVals with
    | error st => exact absurd (Func.run_fromState_stuck M f args (n + j) _ hen _ ht) (hst st)
    | ok p =>
      obtain ⟨body, env⟩ := p
      rw [Func.run_fromState M f args (n + j) _ hen] at ht
      rw [Func.run_fromState M f args n _ hen]
      exact (Func.runOps_memAhead M n j f env body _).finish_down Prod.fst hne hst ht
  constructor
  · intro n m o hnm ho hs
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    cases o with
    | ret _ | ub _ => exact up n j _ (fun h => nomatch h) (fun _ h => nomatch h) hs
    | fuelExhausted => exact absurd rfl ho
  · intro n m o hnm ho ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    cases o with
    | ret _ | ub _ => exact down n j _ (fun h => nomatch h) (fun _ h => nomatch h) ht
    | fuelExhausted => exact absurd rfl ho

end

end Fir
