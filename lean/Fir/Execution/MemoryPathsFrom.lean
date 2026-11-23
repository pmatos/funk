import Fir.Execution.MemoryMonotone
import Fir.Execution.RunPaths

/-!
# Paths from given memories

How a path of a computation of the state layer, read from given memories
(the section on how a run with memory ends), goes on through a check, a
computation of the layer, or a run of ops followed by more: the facts that
the section on a run of ops with memory, one step at a time, builds on.
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

/-! # Runs of ops from given memories -/

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
