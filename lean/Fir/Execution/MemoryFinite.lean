import Fir.Execution.MemoryCalls
import Fir.Execution.MemoryObligationLaws
import Fir.Execution.Modes

/-!
# Ops of finitely many outcomes

Reading divergence as "every budget can be exhausted" assumes that every
choice has finitely many options (the section on observable behaviour). With
memory, an op's outcome is its results, or where control goes, with the
memories it ends with. An op has _finitely many outcomes_ when, from each
memories, the results it may end with and the memories they come with are
among those of a list. UB is not counted: a path that hits UB ends there.

A computation of the set monad that a tree of choices denotes has finitely
many outcomes: a choice of _w_ bits has 2 to the power _w_ options, and each
leaf ends one path. Lifted into the state layer, it keeps the memories and so
keeps finitely many outcomes.

When every op that runs by its own rule has finitely many outcomes, a run of
ops with memory at one budget returns finitely many things, calls and
recursion included: each step goes on in finitely many ways, a callee
returns finitely many things at a smaller budget, and the rest of the run
has a smaller budget too. The proof is by strong induction on the budget,
following the ways a step goes on.
-/

namespace Fir

open SetM Memory

/-! # Finitely many outcomes -/

section

variable {σ α β γ : Type}

/-- A computation of the set monad has finitely many results: each result it
may end with is in a list. -/
def SetM.FinitelyMany (x : SetM α) : Prop :=
  ∃ L : List α, ∀ a, x (.ok a) → a ∈ L

/-- A computation of the state layer has finitely many outcomes: from each
memories, each result it may end with, with the memories it ends with, is in
a list. -/
def FinitelyMany (c : StateT σ SetM α) : Prop :=
  ∀ S, ∃ L : List (α × σ), ∀ x, c S (.ok x) → x ∈ L

/-- A computation of the set monad, lifted into the state layer, keeps
finitely many results: it keeps the memories. -/
theorem FinitelyMany.lift {x : SetM α} (h : x.FinitelyMany) :
    FinitelyMany (σ := σ) (StateT.lift x) := fun S => by
  obtain ⟨L, hL⟩ := h
  refine ⟨L.map (·, S), fun p hp => ?_⟩
  rcases (SetM.lift_apply x S _).1 hp with ⟨a, ha, he⟩ | ⟨_, _, he⟩
  · cases he
    exact List.mem_map.2 ⟨a, hL a ha, rfl⟩
  · cases he

/-- The set of a tree of choices has finitely many results: a choice of `w`
bits has `2 ^ w` options. -/
theorem ChoiceTree.toSet_finitelyMany {ε : Type} : ∀ t : ChoiceTree ε α, t.toSet.FinitelyMany
  | .pure a => ⟨[a], fun _ h => by cases h; exact List.mem_singleton_self _⟩
  | .ub _ => ⟨[], fun _ h => nomatch h⟩
  | .noOutcome _ => ⟨[], fun _ h => h.elim⟩
  | .choose w k => by
    have hk := fun b => ChoiceTree.toSet_finitelyMany (k b)
    refine ⟨(allBits w).flatMap fun b => Classical.choose (hk b), fun a ⟨b, hb⟩ => ?_⟩
    exact List.mem_flatMap.2 ⟨b, mem_allBits b, Classical.choose_spec (hk b) a hb⟩

/-- When each member of a list has a list that covers what it relates to,
one list covers what every member relates to. -/
theorem List.exists_cover {P : α → β → Prop} :
    ∀ {L : List α}, (∀ a ∈ L, ∃ C : List β, ∀ b, P a b → b ∈ C) →
      ∃ C : List β, ∀ a ∈ L, ∀ b, P a b → b ∈ C
  | [], _ => ⟨[], fun _ h => nomatch h⟩
  | a :: L, h => by
    obtain ⟨C₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨C₂, h₂⟩ := List.exists_cover fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    refine ⟨C₁ ++ C₂, fun a' ha' b hb => ?_⟩
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact List.mem_append_left _ (h₁ b hb)
    · exact List.mem_append_right _ (h₂ a' ha' b hb)

/-- When each member of a list has a budget from which on `Q` holds of it,
one budget serves every member. -/
theorem List.exists_budget {Q : α → Nat → Prop} (hQ : ∀ a {m m' : Nat}, m ≤ m' → Q a m → Q a m') :
    ∀ {L : List α}, (∀ a ∈ L, ∃ m, Q a m) → ∃ m, ∀ a ∈ L, Q a m
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | a :: L, h => by
    obtain ⟨m₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨m₂, h₂⟩ := List.exists_budget hQ fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    refine ⟨max m₁ m₂, fun a' ha' => ?_⟩
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact hQ _ (Nat.le_max_left _ _) h₁
    · exact hQ _ (Nat.le_max_right _ _) (h₂ a' ha')

/-- A run returns finitely many things: each thing it may return is in a
list. -/
def FinitelyManyRets (s : ExceptT Stuck SetM (Result β)) : Prop :=
  ∃ L : List β, ∀ b, s.run (.ok (.ok (.ret b))) → b ∈ L

/-- A run with its returns mapped returns finitely many things when the run
does. -/
theorem FinitelyManyRets.mapVal {s : ExceptT Stuck SetM (Result (α × Nat))} (F : α → γ)
    (h : FinitelyManyRets s) : FinitelyManyRets (Result.mapVal F <$> s) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L.map fun p => (F p.1, p.2), fun b hb => ?_⟩
  rcases (SetM.run_map _ _ _).1 hb with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · match r, hr, he with
    | .ret (a, k), hr, he =>
      cases he
      exact List.mem_map.2 ⟨(a, k), hL _ hr, rfl⟩
    | .fuelExhausted, _, he => cases he
  · cases he
  · cases he

end

/-! # Ops of finitely many outcomes -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-- Every op of `d` that runs by its own rule, a terminator or an op with no
callee, has finitely many outcomes with memory, from each operands, as an op
that is not a terminator and as a terminator. -/
def OpsFinite (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectCall d] (Mem : Type)
    (unit : Mem → Nat) [DialectDenote d (StateT (Memories Mem unit) SetM)] : Prop :=
  ∀ op : d.Op, isTerminator op = true ∨ callee? op = none → ∀ args : HVector toType (sig op),
    (isTerminator op = false →
      FinitelyMany (DialectDenote.denote (m := StateT (Memories Mem unit) SetM) op args)) ∧
    (isTerminator op = true →
      FinitelyMany (DialectDenote.exit (m := StateT (Memories Mem unit) SetM) op args))

/-! # Runs at a budget -/

section

variable {M : Module d} {g : Func d} {genv : Env d} {body : List (Operation d)}
  {S : Memories Mem unit}

/-- A run in a call's frame runs out of fuel exactly when its ops do, from
the memories with a frame entered. -/
theorem Func.memCall_exhausted_iff {n : Nat} :
    (Func.memCall M n g genv body S).run (.ok (.ok .fuelExhausted)) ↔
      (Func.memOps M n g genv body S.enter).run (.ok (.ok .fuelExhausted)) := by
  rw [Func.memCall_eq]
  constructor
  · intro h
    rcases (SetM.run_map _ _ _).1 h with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · match r, hr, he with
      | .fuelExhausted, hr, _ => exact hr
      | .ret _, _, he => cases he
    · cases he
    · cases he
  · exact fun h => (SetM.run_map _ _ _).2 (.inl ⟨_, h, rfl⟩)

/-- UB of a callee's ops is UB of the callee in its frame. -/
theorem Func.memCall_ub_of_memOps {n : Nat} {r : String}
    (h : (Func.memOps M n g genv body S.enter).run (.ub r)) :
    (Func.memCall M n g genv body S).run (.ub r) := by
  rw [Func.memCall_eq]
  exact (SetM.run_map _ _ _).2 (.inr (.inr ⟨r, h, rfl⟩))

/-- A run of ops with memory that does not run out of fuel at a budget does
not at any larger one. -/
theorem Func.memOps_notExhausted_up {f : Func d} {env : Env d} {os : List (Operation d)}
    {m m' : Nat} (hle : m ≤ m')
    (h : ¬ (Func.memOps M m f env os S).run (.ok (.ok .fuelExhausted))) :
    ¬ (Func.memOps M m' f env os S).run (.ok (.ok .fuelExhausted)) := fun h' => h (by
  have := Func.memOps_exhausted_down M m (m' - m) f env os S
  rw [Nat.add_sub_cancel' hle] at this
  exact this h')

/-- A run in a call's frame that does not run out of fuel at a budget does
not at any larger one. -/
theorem Func.memCall_notExhausted_up {m m' : Nat} (hle : m ≤ m')
    (h : ¬ (Func.memCall M m g genv body S).run (.ok (.ok .fuelExhausted))) :
    ¬ (Func.memCall M m' g genv body S).run (.ok (.ok .fuelExhausted)) := fun h' =>
  Func.memOps_notExhausted_up hle (mt Func.memCall_exhausted_iff.2 h)
    (Func.memCall_exhausted_iff.1 h')

end

/-- A run of ops with memory at one budget returns finitely many things,
from any environment and memories, calls and recursion included, when every
op that runs by its own rule has finitely many outcomes. -/
theorem Func.memOps_finitelyManyRets (hfin : OpsFinite d Mem unit) (M : Module d) (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)) (S : Memories Mem unit),
      FinitelyManyRets (Func.memOps M n f env os S) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os S
    match n, os with
    | 0, _ => exact ⟨[], fun _ h => nomatch Func.run_memOps_zero.1 h⟩
    | n + 1, [] => exact ⟨[], fun _ h => absurd h (Func.run_memOps_nil (fun _ h => nomatch h))⟩
    | n + 1, o :: os =>
      have ihn := ih n (Nat.lt_succ_self n)
      have path := fun {b} (h : (Func.memOps M (n + 1) f env (o :: os) S).run (.ok (.ok (.ret b)))) =>
        (Func.memStepPath_iff (e := .ok (.ok (.ret b))) (fun _ h => nomatch h)).1 h
      cases hargs : env.operands (sig o.op) o.operands with
      | error _ =>
        refine ⟨[], fun b h => ?_⟩
        cases path h <;> simp_all
      | ok args =>
        have same : ∀ {a}, env.operands (sig o.op) o.operands = .ok a → a = args :=
          fun h => Except.ok.inj (h.symm.trans hargs)
        by_cases hT : isTerminator o.op = true
        · obtain ⟨LE, hLE⟩ := (hfin o.op (.inl hT) args).2 hT S
          obtain ⟨C, hC⟩ := List.exists_cover (P := fun (p : Exit × Memories Mem unit) b =>
            ∃ i blk env₁, p.1 = .goto i ∧ f.jump env o.succs i = .ok (blk, env₁) ∧
              (Func.memOps M n f env₁ blk.body p.2).run (.ok (.ok (.ret b)))) (L := LE)
            fun ⟨x, S'⟩ _ => by
              cases x with
              | ret => exact ⟨[], fun _ ⟨_, _, _, h, _⟩ => nomatch h⟩
              | goto i =>
                cases hj : f.jump env o.succs i with
                | error _ => exact ⟨[], fun _ ⟨_, _, _, hi, h, _⟩ => by cases hi; simp_all⟩
                | ok p =>
                  obtain ⟨C, hC⟩ := ihn f p.2 p.1.body S'
                  refine ⟨C, fun b ⟨i', blk, env₁, hi, h, hb⟩ => ?_⟩
                  cases hi
                  rw [hj] at h
                  cases h
                  exact hC b hb
          refine ⟨LE.map (fun p => ((args.toDVals, p.2), n)) ++ C, fun b h => ?_⟩
          cases path h with
          | ret _ hargs' _ _ hx _ =>
            cases same hargs'
            exact List.mem_append_left _ (List.mem_map.2 ⟨_, hLE _ hx, rfl⟩)
          | goto _ hargs' _ _ hx hj h =>
            cases same hargs'
            exact List.mem_append_right _ (hC _ (hLE _ hx) b ⟨_, _, _, rfl, hj, h⟩)
          | denote _ _ hT' => exact absurd hT (by simp [hT'])
          | callRet _ _ hT' => exact absurd hT (by simp [hT'])
        cases hc : callee? o.op with
        | none =>
          have hT' : isTerminator o.op = false := by simpa using hT
          obtain ⟨LD, hLD⟩ := (hfin o.op (.inr hc) args).1 hT' S
          obtain ⟨C, hC⟩ := List.exists_cover (L := LD) (P := fun p b =>
            (o.results.map (·.1)).length = p.1.toDVals.length ∧
              (Func.memOps M n f ((o.results.map (·.1)).zip p.1.toDVals ++ env) os p.2).run
                (.ok (.ok (.ret b))))
            fun p _ => by
              obtain ⟨C, hC⟩ := ihn f ((o.results.map (·.1)).zip p.1.toDVals ++ env) os p.2
              exact ⟨C, fun b h => hC b h.2⟩
          refine ⟨C, fun b h => ?_⟩
          cases path h with
          | ret _ _ hT' => exact absurd hT' hT
          | goto _ _ hT' => exact absurd hT' hT
          | denote _ hargs' _ _ hx hlen h =>
            cases same hargs'
            exact hC _ (hLD _ hx) b ⟨hlen, h⟩
          | callRet _ _ _ hc' => simp_all
        | some s =>
          cases hg : M.func? s with
          | none =>
            refine ⟨[], fun b h => ?_⟩
            cases path h <;> simp_all
          | some g =>
            cases hen : g.enter args.toDVals with
            | error _ =>
              refine ⟨[], fun b h => ?_⟩
              cases path h <;> simp_all
            | ok p =>
              obtain ⟨LC, hLC⟩ : FinitelyManyRets (Func.memCall M n g p.2 p.1 S) := by
                rw [Func.memCall_eq]
                exact (ihn g p.2 p.1 S.enter).mapVal _
              obtain ⟨C, hC⟩ := List.exists_cover (L := LC) (P := fun (r : (List (DVal d) ×
                  Memories Mem unit) × Nat) b =>
                (Func.memOps M (min r.2 n) f ((o.results.map (·.1)).zip r.1.1 ++ env) os
                  r.1.2).run (.ok (.ok (.ret b))))
                fun r _ => ih (min r.2 n) (Nat.lt_succ_of_le (Nat.min_le_right _ _)) f _ os _
              refine ⟨C, fun b h => ?_⟩
              cases path h with
              | ret _ _ hT' => exact absurd hT' hT
              | goto _ _ hT' => exact absurd hT' hT
              | denote _ _ _ hc' => simp_all
              | callRet _ hargs' _ hc' hg' hen' hx _ _ h =>
                cases same hargs'
                rw [hc'] at hc
                cases hc
                rw [hg'] at hg
                cases hg
                rw [hen'] at hen
                cases hen
                exact hC _ (hLC _ hx) b h

/-- A run in a call's frame at one budget returns finitely many things, from
any memories, when every op that runs by its own rule has finitely many
outcomes. -/
theorem Func.memCall_finitelyManyRets (hfin : OpsFinite d Mem unit) (M : Module d) (n : Nat)
    (g : Func d) (genv : Env d) (body : List (Operation d)) (S : Memories Mem unit) :
    FinitelyManyRets (Func.memCall M n g genv body S) := by
  rw [Func.memCall_eq]
  exact (Func.memOps_finitelyManyRets hfin M n g genv body S.enter).mapVal _

end Fir
