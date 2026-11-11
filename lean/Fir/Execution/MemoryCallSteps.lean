import Fir.Execution.MemoryMonotone
import Fir.Execution.MemoryObligationLaws

/-!
# The steps of a call, with memory

Progress with calls rests on the facts of the section on the steps of a
call. Those that speak of scope, of entering a function and of the symbol
table do not look at how a run computes, so they hold of runs with memory
as they are. The others are read here from given memories (the section on
how a run with memory ends):

* _A sequence has no stuck path, and has a path, when its parts do._ The
  second part runs from the memories that the first ended with, so it must
  have them from each of those memories.
* _A function returns values of its result types_, with memory too: the
  interpreter checks the types of the values that a function returns
  before it returns them, whatever its ops do to the memories, and a call's
  frame changes only the memories.
* _A function runs within its module, with memory_: as in the section on
  progress with calls, but each terminator keeps to its rules from any
  memories. A terminator whose exit goes to a successor names one that it
  has and gives no results, and one whose exit returns returns values of
  the function's result types. For a dialect that lifts the set monad, a
  function that runs within its module runs within it with memory, at
  every naming: its terminators go where they go in the set monad, and
  keep the memories.
-/

namespace Fir

open SetM Memory

variable {σ ε α β : Type}

/-! # Paths from given memories -/

/-- A check of the interpreter that passes gives way to what follows it. -/
theorem liftExcept_ok_bind {m : Type → Type} [Monad m] [LawfulMonad m] (a : α)
    (g : α → ExceptT ε m β) : (liftExcept (Except.ok a : Except ε α) : ExceptT ε m α) >>= g = g a :=
  pure_bind a g

/-- A computation mapped has no stuck path when it has none. -/
theorem NoStuck.map {s : ExceptT Stuck SetM α} (f : α → β) (h : NoStuck s) : NoStuck (f <$> s) :=
  fun st hs => by
    rcases (SetM.run_map f s _).1 hs with ⟨_, _, he⟩ | ⟨er, her, he⟩ | ⟨_, _, he⟩
    · cases he
    · cases he
      exact h _ her
    · cases he

/-- A computation mapped has a path when it has one. -/
theorem HasPath.map {s : ExceptT Stuck SetM α} (f : α → β) (h : HasPath s) : HasPath (f <$> s) := by
  obtain ⟨e, he⟩ := h
  match e, he with
  | .ok (.ok a), he => exact ⟨_, (SetM.run_map f s _).2 (.inl ⟨a, he, rfl⟩)⟩
  | .ok (.error er), he => exact ⟨_, (SetM.run_map f s _).2 (.inr (.inl ⟨er, he, rfl⟩))⟩
  | .ub r, he => exact ⟨_, (SetM.run_map f s _).2 (.inr (.inr ⟨r, he, rfl⟩))⟩

variable {x : ExceptT Stuck (StateT σ SetM) α} {g : α → ExceptT Stuck (StateT σ SetM) β} {S : σ}

/-- `x >>= g`, from `S`, has no stuck path when `x` has none from `S`, and
`g` has none on each result of `x` from the memories it ended with. -/
theorem NoStuck.fromState_bind (hx : NoStuck (fromState x S))
    (hg : ∀ a S', (fromState x S).run (.ok (.ok (a, S'))) → NoStuck (fromState (g a) S')) :
    NoStuck (fromState (x >>= g) S) := by
  rw [Fir.fromState_bind]
  exact NoStuck.bind hx fun p hp => hg p.1 p.2 hp

/-- `x >>= g`, from `S`, has a path when `x` has one from `S`, and `g` has
one on each result of `x` from the memories it ended with. -/
theorem HasPath.fromState_bind (hx : HasPath (fromState x S))
    (hg : ∀ a S', (fromState x S).run (.ok (.ok (a, S'))) → HasPath (fromState (g a) S')) :
    HasPath (fromState (x >>= g) S) := by
  rw [Fir.fromState_bind]
  exact HasPath.bind hx fun p hp => hg p.1 p.2 hp

/-- A computation of the layer, lifted, is never stuck. -/
theorem NoStuck.fromState_lift (c : StateT σ SetM α) (S : σ) :
    NoStuck (fromState (ExceptT.lift c : ExceptT Stuck (StateT σ SetM) α) S) := by
  rw [Fir.fromState_lift]
  exact NoStuck.lift

/-- A computation of the layer, lifted, has a path from `S` when it has an
outcome from `S`. -/
theorem HasPath.fromState_lift {c : StateT σ SetM α} (h : ∃ e, c S e) :
    HasPath (fromState (ExceptT.lift c : ExceptT Stuck (StateT σ SetM) α) S) := by
  rw [Fir.fromState_lift]
  obtain ⟨e, he⟩ := h
  cases e with
  | ok p => exact ⟨_, (run_lift _ _).2 (.inl ⟨p, he, rfl⟩)⟩
  | ub r => exact ⟨_, (run_lift _ _).2 (.inr ⟨r, he, rfl⟩)⟩

/-- A way that a computation of the layer, lifted, ends with a result from
`S` is a way that it ends from `S`. -/
theorem fromState_lift_ok {c : StateT σ SetM α} {a : α} {S' : σ}
    (h : (fromState (ExceptT.lift c : ExceptT Stuck (StateT σ SetM) α) S).run (.ok (.ok (a, S')))) :
    c S (.ok (a, S')) := by
  rw [fromState_lift] at h
  rcases (run_lift _ _).1 h with ⟨_, h, he⟩ | ⟨_, _, he⟩
  · cases he
    exact h
  · cases he

/-! # A function returns values of its result types -/

section

variable {d : Dialect} [TyDenote d.Ty]

/-- Every return of `x`, from any memories, returns values of the types
`ts`. -/
def MemReturnsTypes (ts : List d.Ty)
    (x : ExceptT Stuck (StateT σ SetM) (Result (List (DVal d) × Nat))) : Prop :=
  ∀ S vs k S', (fromState x S).run (.ok (.ok (.ret (vs, k), S'))) → vs.map (·.1) = ts

namespace MemReturnsTypes

variable {ts : List d.Ty}

/-- `x >>= g` returns values of the types `ts` when `g` does on each
result. -/
theorem bind {β : Type} {x : ExceptT Stuck (StateT σ SetM) β}
    {g : β → ExceptT Stuck (StateT σ SetM) (Result (List (DVal d) × Nat))}
    (h : ∀ b, MemReturnsTypes ts (g b)) : MemReturnsTypes ts (x >>= g) := by
  intro S vs k S' hk
  rw [fromState_bind] at hk
  rcases (run_bind _ _ _).1 hk with ⟨p, _, hg⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · exact h p.1 p.2 vs k S' hg
  · cases he
  · cases he

/-- A stuck computation returns nothing. -/
theorem of_stuck {r : String} :
    MemReturnsTypes ts (liftExcept (stuck r) :
      ExceptT Stuck (StateT σ SetM) (Result (List (DVal d) × Nat))) := by
  intro S _ _ _ hk
  rw [fromState_liftExcept] at hk
  exact nomatch (run_liftExcept _ _).1 hk

/-- A run that runs out of fuel returns nothing. -/
theorem exhausted :
    MemReturnsTypes ts (pure .fuelExhausted :
      ExceptT Stuck (StateT σ SetM) (Result (List (DVal d) × Nat))) := by
  intro S _ _ _ hk
  rw [fromState_pure] at hk
  exact nomatch (run_pure _ _).1 hk

/-- A return of values of the types `ts`. -/
theorem ret {vs : List (DVal d)} {k : Nat} (h : vs.map (·.1) = ts) :
    MemReturnsTypes ts (pure (.ret (vs, k)) :
      ExceptT Stuck (StateT σ SetM) (Result (List (DVal d) × Nat))) := by
  intro S _ _ _ hk
  rw [fromState_pure] at hk
  cases (run_pure _ _).1 hk
  exact h

/-- A run in a call's frame returns what the run returns. -/
theorem inFrame {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
    {x : ExceptT Stuck (StateT (Memories Mem unit) SetM) (Result (List (DVal d) × Nat))}
    (h : MemReturnsTypes ts x) : MemReturnsTypes ts (Fir.inFrame x) := by
  intro S vs k S' hk
  rw [fromState_inFrame] at hk
  rcases (SetM.run_map _ _ _).1 hk with ⟨p, hp, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · obtain ⟨r, S''⟩ := p
    cases he
    exact h _ vs k S'' hp
  · cases he
  · cases he

end MemReturnsTypes

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-- A run of ops of `f` with memory returns values of `f`'s result types,
from any memories: the interpreter checks them before it returns. -/
theorem Func.runOps_memReturns (M : Module d) (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)),
      MemReturnsTypes f.results (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env os) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os
    match n, os with
    | 0, _ => simp only [Func.runOps]; exact MemReturnsTypes.exhausted
    | _ + 1, [] => simp only [Func.runOps]; exact MemReturnsTypes.of_stuck
    | k + 1, o :: os =>
      simp only [Func.runOps]
      all_goals repeat' (first
        | (apply MemReturnsTypes.bind; intro _)
        | split
        | exact MemReturnsTypes.of_stuck
        | exact MemReturnsTypes.exhausted
        | exact MemReturnsTypes.ret (by rw [HVector.toDVals_types]; assumption)
        | exact ih _ (Nat.lt_succ_self _) _ _ _
        | exact ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _)

/-! # Running within a module, with memory -/

variable (unit) in
/-- The ops of `f` run within the module `M` with memory: an op that calls
a function names a symbol of `M` whose type is the call's; from any
memories, a terminator that goes to a successor names one that it has and
gives no results, and a terminator that returns returns values of `f`'s
result types. -/
structure Func.MemInModule (M : Module d) (f : Func d) : Prop where
  calls : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = false → ∀ s,
    callee? o.op = some s → M.symbols s = some ⟨sig o.op, returnTypes o.op⟩
  jumps : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → ∀ args S i S',
    DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args S (.ok (.goto i, S')) →
      i < succCount o.op ∧ returnTypes o.op = []
  returns : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → ∀ args S S',
    DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args S (.ok (.ret, S')) →
      sig o.op = f.results

end

/-! # Running within a module, at a naming -/

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectCall d] {N : Type}
  [DecidableEq N] (unit : N → Nat) {M : Module d}

omit [DecidableEq N] in
/-- A function that runs within its module runs within it with memory, by
its dialect's semantics in the set monad lifted into the state layer: each
terminator goes where it goes in the set monad, from any memories. -/
theorem Func.InModule.memInModule_liftState [DialectDenote d SetM] {f : Func d}
    (h : f.InModule M) :
    letI := DialectDenote.liftState (m := SetM) (d := d) (Memories N unit)
    f.MemInModule unit M := by
  letI := DialectDenote.liftState (m := SetM) (d := d) (Memories N unit)
  have ex : ∀ {op : d.Op} {args : HVector toType (sig op)} {S : Memories N unit} {x : Exit}
      {S' : Memories N unit}, DialectDenote.exit (m := StateT (Memories N unit) SetM) op args S
        (.ok (x, S')) → DialectDenote.exit (m := SetM) op args (.ok x) := fun hx => by
    rcases (SetM.lift_apply _ _ _).1 hx with ⟨_, hc, he⟩ | ⟨_, _, he⟩
    · cases he
      exact hc
    · cases he
  exact ⟨h.calls, fun b hb o ho hT args _ i _ hx => h.jumps b hb o ho hT args i (ex hx),
    fun b hb o ho hT args _ _ hx => h.returns b hb o ho hT args (ex hx)⟩

variable [DialectEffects d] [DialectMemDenote d] (ρ : DialectEffects.Mem d → N)

/-- The ops of `f` run within the module `M` with memory, where a run names
the dialect's memory `x` as `ρ x`, whose units are `unit (ρ x)` bits wide:
they run within it by the dialect's semantics with memory at that naming. -/
def Func.InModuleAt (M : Module d) (f : Func d) : Prop :=
  letI := DialectMemDenote.denoteAt (d := d) unit ρ
  f.MemInModule unit M

/-- A run with memory of a function that starts, at a budget, at a naming:
its entry block's ops, run from the empty memories with a frame entered,
finished. -/
theorem Func.memRuns_enter [DecidableEq d.Ty] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (n : Nat) {body : List (Operation d)}
    {env : Env d} (hen : f.enter args.toDVals = .ok (body, env)) :
    letI := DialectMemDenote.denoteAt (d := d) unit ρ
    f.memRuns unit ρ M args n = (Result.finish Prod.fst
      (runFrom (Func.runOps (m := StateT (Memories N unit) SetM) M n f env body)
        Memories.empty.enter)).run := by
  letI := DialectMemDenote.denoteAt (d := d) unit ρ
  rw [← Func.run_fromState M f args n _ hen]
  exact fromState_fst _ _

/-- A function that runs within its module runs within it with memory,
wherever a run names the memories of a dialect that lifts the set monad. -/
theorem Func.InModule.inModuleAt [DialectDenote d SetM] [LiftsSetM d] {f : Func d}
    (h : f.InModule M) : f.InModuleAt unit ρ M := by
  unfold Func.InModuleAt
  rw [LiftsSetM.lifts unit ρ]
  exact h.memInModule_liftState unit

end

end Fir
