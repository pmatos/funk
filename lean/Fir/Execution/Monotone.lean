import Fir.Execution.SetRuns
import Fir.Execution.Interpreter
import Fir.Execution.Refinement

/-!
# Runs at every budget

The runs of a function of a module are its runs in the set monad, on each
argument vector of its parameter types, at each budget. Their observable
behaviour is what the function does.

They are fuel-monotone, for every function of every module of every dialect,
whatever its ops do. Of a function that reaches an op without rules, this holds
only vacuously on the paths that reach the op
(`docs/decisions/fir-ref.md#an-op-without-rules`). The proof needs no property
of the ops, because the interpreter alone counts the fuel: an op never sees it,
and a call hands its callee the steps that the caller has left and goes on with
what the callee gives back. It rests on two facts, each proved by induction on
the budget:

* _A run gives back at most the fuel it was given_, so a caller goes on
  with exactly the steps its callee leaves.
* _A run with more steps of fuel is ahead by as many steps._ Each of its
  returns is a return of the smaller run that leaves that many fewer
  steps, or the smaller run can run out of fuel. Each of the smaller run's
  returns leaves that many more steps in it, and the two hit the same UB.
  A call keeps this: its callee, run with more steps, gives back as many
  more, so its caller goes on with as many more.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- The runs of the function `f` of the module `M`: on each argument vector
of its parameter types, its run in the set monad at each budget. -/
def Func.runs (M : Module d) (f : Func d) :
    FuncRuns (HVector toType (f.params.map (·.2))) (List (DVal d)) :=
  fun args fuel => f.run M (m := SetM) args fuel

/-! # A run leaves at most its budget -/

/-- Every return of `s` leaves at most `n` steps. -/
def LeavesAtMost (n : Nat) (s : ExceptT Stuck SetM (Result (α × Nat))) : Prop :=
  ∀ a k, s.run (.ok (.ok (.ret (a, k)))) → k ≤ n

namespace LeavesAtMost

/-- `x >>= g` leaves at most `n` steps when `g` does on each result of `x`. -/
theorem bind {n : Nat} {x : ExceptT Stuck SetM β} {g : β → ExceptT Stuck SetM (Result (α × Nat))}
    (h : ∀ b, x.run (.ok (.ok b)) → LeavesAtMost n (g b)) : LeavesAtMost n (x >>= g) := by
  intro a k hk
  rcases (run_bind x g _).1 hk with ⟨b, hb, hg⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · exact h b hb a k hg
  · cases he
  · cases he

/-- A stuck computation returns nothing. -/
theorem of_stuck {n : Nat} {r : String} : LeavesAtMost n (liftExcept (stuck r) : ExceptT Stuck SetM (Result (α × Nat))) :=
  fun _ _ hk => nomatch (run_liftExcept _ _).1 hk

/-- A run that runs out of fuel returns nothing. -/
theorem exhausted {n : Nat} : LeavesAtMost n (pure .fuelExhausted : ExceptT Stuck SetM (Result (α × Nat))) :=
  fun _ _ hk => nomatch (run_pure _ _).1 hk

/-- A return that leaves `k ≤ n` steps leaves at most `n`. -/
theorem ret {n k : Nat} {a : α} (h : k ≤ n) : LeavesAtMost n (pure (.ret (a, k)) : ExceptT Stuck SetM (Result (α × Nat))) :=
  fun _ _ hk => by cases (run_pure _ _).1 hk; exact h

/-- A bound on the steps left holds for every larger bound. -/
theorem mono {n n' : Nat} {s : ExceptT Stuck SetM (Result (α × Nat))} (h : n ≤ n') (hs : LeavesAtMost n s) :
    LeavesAtMost n' s :=
  fun a k hk => Nat.le_trans (hs a k hk) h

end LeavesAtMost

/-- A run of ops gives back at most the steps of fuel it was given. -/
theorem Func.runOps_left_le (M : Module d) (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)),
      LeavesAtMost n (Func.runOps (m := SetM) M n f env os) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os
    match n, os with
    | 0, _ => simp only [Func.runOps]; exact LeavesAtMost.exhausted
    | _ + 1, [] => simp only [Func.runOps]; exact LeavesAtMost.of_stuck
    | k + 1, o :: os =>
      simp only [Func.runOps]
      all_goals repeat' (first
        | (apply LeavesAtMost.bind; intro _ _)
        | split
        | exact LeavesAtMost.of_stuck
        | exact LeavesAtMost.exhausted
        | exact LeavesAtMost.ret (Nat.le_succ _)
        | exact (ih _ (Nat.lt_succ_self _) _ _ _).mono (Nat.le_succ _)
        | exact (ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _).mono
            (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_succ _)))

/-! # A run with more fuel -/

/-- The run `t` is the run `s` with `j` more steps of fuel. Each return of
`s` is a return of `t` that leaves `j` more steps, and each UB of `s` is
one of `t`. Each return of `t` is a return of `s` that leaves `j` fewer
steps, unless `s` can run out of fuel, and so is each UB of `t`. -/
structure Ahead (j : Nat) (s t : ExceptT Stuck SetM (Result (α × Nat))) : Prop where
  up_ret : ∀ a k, s.run (.ok (.ok (.ret (a, k)))) → t.run (.ok (.ok (.ret (a, k + j))))
  up_ub : ∀ r, s.run (.ub r) → t.run (.ub r)
  down_ret : ∀ a k, t.run (.ok (.ok (.ret (a, k)))) →
    (j ≤ k ∧ s.run (.ok (.ok (.ret (a, k - j))))) ∨ s.run (.ok (.ok .fuelExhausted))
  down_ub : ∀ r, t.run (.ub r) → s.run (.ub r) ∨ s.run (.ok (.ok .fuelExhausted))

namespace Ahead

variable {j : Nat}

/-- The same first computation, then continuations of which one is ahead
of the other. -/
theorem bind {x : ExceptT Stuck SetM β} {g h : β → ExceptT Stuck SetM (Result (α × Nat))}
    (hgh : ∀ b, x.run (.ok (.ok b)) → Ahead j (g b) (h b)) : Ahead j (x >>= g) (x >>= h) where
  up_ret a k hs := by
    rcases (run_bind x g _).1 hs with ⟨b, hb, hg⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · exact (run_bind x h _).2 (.inl ⟨b, hb, (hgh b hb).up_ret a k hg⟩)
    · cases he
    · cases he
  up_ub r hs := by
    rcases (run_bind x g _).1 hs with ⟨b, hb, hg⟩ | ⟨_, _, he⟩ | ⟨r', hr, he⟩
    · exact (run_bind x h _).2 (.inl ⟨b, hb, (hgh b hb).up_ub r hg⟩)
    · cases he
    · exact (run_bind x h _).2 (.inr (.inr ⟨r', hr, he⟩))
  down_ret a k ht := by
    rcases (run_bind x h _).1 ht with ⟨b, hb, hh⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · rcases (hgh b hb).down_ret a k hh with ⟨hj, hs⟩ | hs
      · exact .inl ⟨hj, (run_bind x g _).2 (.inl ⟨b, hb, hs⟩)⟩
      · exact .inr ((run_bind x g _).2 (.inl ⟨b, hb, hs⟩))
    · cases he
    · cases he
  down_ub r ht := by
    rcases (run_bind x h _).1 ht with ⟨b, hb, hh⟩ | ⟨_, _, he⟩ | ⟨r', hr, he⟩
    · rcases (hgh b hb).down_ub r hh with hs | hs
      · exact .inl ((run_bind x g _).2 (.inl ⟨b, hb, hs⟩))
      · exact .inr ((run_bind x g _).2 (.inl ⟨b, hb, hs⟩))
    · cases he
    · exact .inl ((run_bind x g _).2 (.inr (.inr ⟨r', hr, he⟩)))

/-- A run of a callee, then what its caller does with the result: when
the callee with more fuel is ahead, and so is what the caller does with a
return that leaves `j` more steps, so is the whole. A callee that runs out
of fuel ends its caller so. -/
theorem bindRun {n : Nat} {x y : ExceptT Stuck SetM (Result (β × Nat))} {g h : Result (β × Nat) → ExceptT Stuck SetM (Result (α × Nat))}
    (hxy : Ahead j x y) (hx : LeavesAtMost n x) (hg : g .fuelExhausted = pure .fuelExhausted)
    (hh : h .fuelExhausted = pure .fuelExhausted)
    (hgh : ∀ b k, k ≤ n → Ahead j (g (.ret (b, k))) (h (.ret (b, k + j)))) :
    Ahead j (x >>= g) (y >>= h) where
  up_ret a k hs := by
    rcases (run_bind x g _).1 hs with ⟨r, hr, hgr⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · match r, hr, hgr with
      | .fuelExhausted, _, hgr => rw [hg] at hgr; exact nomatch (run_pure _ _).1 hgr
      | .ret (b, k'), hr, hgr =>
        exact (run_bind y h _).2 (.inl ⟨_, hxy.up_ret b k' hr,
          (hgh b k' (hx b k' hr)).up_ret a k hgr⟩)
    · cases he
    · cases he
  up_ub r hs := by
    rcases (run_bind x g _).1 hs with ⟨r', hr, hgr⟩ | ⟨_, _, he⟩ | ⟨r', hr, he⟩
    · match r', hr, hgr with
      | .fuelExhausted, _, hgr => rw [hg] at hgr; exact nomatch (run_pure _ _).1 hgr
      | .ret (b, k'), hr, hgr =>
        exact (run_bind y h _).2 (.inl ⟨_, hxy.up_ret b k' hr,
          (hgh b k' (hx b k' hr)).up_ub r hgr⟩)
    · cases he
    · exact (run_bind y h _).2 (.inr (.inr ⟨r', hxy.up_ub r' hr, he⟩))
  down_ret a k ht := by
    rcases (run_bind y h _).1 ht with ⟨r, hr, hhr⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · match r, hr, hhr with
      | .fuelExhausted, _, hhr => rw [hh] at hhr; exact nomatch (run_pure _ _).1 hhr
      | .ret (b, k'), hr, hhr =>
        rcases hxy.down_ret b k' hr with ⟨hj, hxr⟩ | hxe
        · have hgh' := hgh b (k' - j) (hx b _ hxr)
          rw [Nat.sub_add_cancel hj] at hgh'
          rcases hgh'.down_ret a k hhr with ⟨hj', hs⟩ | hs
          · exact .inl ⟨hj', (run_bind x g _).2 (.inl ⟨_, hxr, hs⟩)⟩
          · exact .inr ((run_bind x g _).2 (.inl ⟨_, hxr, hs⟩))
        · exact .inr ((run_bind x g _).2 (.inl ⟨_, hxe, by rw [hg]; rfl⟩))
    · cases he
    · cases he
  down_ub r ht := by
    rcases (run_bind y h _).1 ht with ⟨r', hr, hhr⟩ | ⟨_, _, he⟩ | ⟨r', hr, he⟩
    · match r', hr, hhr with
      | .fuelExhausted, _, hhr => rw [hh] at hhr; exact nomatch (run_pure _ _).1 hhr
      | .ret (b, k'), hr, hhr =>
        rcases hxy.down_ret b k' hr with ⟨hj, hxr⟩ | hxe
        · have hgh' := hgh b (k' - j) (hx b _ hxr)
          rw [Nat.sub_add_cancel hj] at hgh'
          rcases hgh'.down_ub r hhr with hs | hs
          · exact .inl ((run_bind x g _).2 (.inl ⟨_, hxr, hs⟩))
          · exact .inr ((run_bind x g _).2 (.inl ⟨_, hxr, hs⟩))
        · exact .inr ((run_bind x g _).2 (.inl ⟨_, hxe, by rw [hg]; rfl⟩))
    · cases he
    · rcases hxy.down_ub r' hr with hxu | hxe
      · exact .inl ((run_bind x g _).2 (.inr (.inr ⟨r', hxu, he⟩)))
      · exact .inr ((run_bind x g _).2 (.inl ⟨_, hxe, by rw [hg]; rfl⟩))

/-- A stuck path is the same with more fuel. -/
theorem of_stuck {r : String} : Ahead j (liftExcept (stuck r) : ExceptT Stuck SetM (Result (α × Nat))) (liftExcept (stuck r)) where
  up_ret _ _ hs := nomatch (run_liftExcept _ _).1 hs
  up_ub _ hs := nomatch (run_liftExcept _ _).1 hs
  down_ret _ _ ht := nomatch (run_liftExcept _ _).1 ht
  down_ub _ ht := nomatch (run_liftExcept _ _).1 ht

/-- A run that runs out of fuel has more fuel ahead of it, whatever the
larger run does. -/
theorem exhausted {t : ExceptT Stuck SetM (Result (α × Nat))} : Ahead j (pure .fuelExhausted) t where
  up_ret _ _ hs := nomatch (run_pure _ _).1 hs
  up_ub _ hs := nomatch (run_pure _ _).1 hs
  down_ret _ _ _ := .inr rfl
  down_ub _ _ := .inr rfl

/-- A return leaves `j` more steps with `j` more steps of fuel. -/
theorem ret {a : α} {k : Nat} : Ahead j (pure (.ret (a, k))) (pure (.ret (a, k + j))) where
  up_ret _ _ hs := by cases (run_pure _ _).1 hs; rfl
  up_ub _ hs := nomatch (run_pure _ _).1 hs
  down_ret _ _ ht := by cases (run_pure _ _).1 ht; exact .inl ⟨Nat.le_add_left _ _, by
    rw [Nat.add_sub_cancel]; rfl⟩
  down_ub _ ht := nomatch (run_pure _ _).1 ht

end Ahead

/-- A run of ops with `j` more steps of fuel is ahead of the run with
fewer, calls included. -/
theorem Func.runOps_ahead (M : Module d) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)),
      Ahead j (Func.runOps (m := SetM) M n f env os) (Func.runOps M (n + j) f env os) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os
    match n, os with
    | 0, _ => simp only [Func.runOps]; exact Ahead.exhausted
    | k + 1, [] =>
      rw [Nat.add_right_comm]
      simp only [Func.runOps]
      exact Ahead.of_stuck
    | k + 1, o :: os =>
      rw [Nat.add_right_comm]
      simp only [Func.runOps]
      all_goals repeat' (first
        | (apply Ahead.bind; intro _ _)
        | (refine Ahead.bindRun (ih _ (Nat.lt_succ_self _) _ _ _ _)
            (Func.runOps_left_le _ _ _ _ _) ?_ ?_ ?_
           · rfl
           · rfl
           intro _ _ hk
           dsimp only)
        | split
        | exact Ahead.of_stuck
        | exact Ahead.ret
        | exact ih _ (Nat.lt_succ_self _) _ _ _ _
        | (rw [Nat.min_eq_left hk, Nat.min_eq_left (Nat.add_le_add_right hk _)]
           exact ih _ (Nat.lt_succ_of_le hk) _ _ _ _))

/-! # The run of a function -/

/-- A way a run of ops ends, without the steps it leaves: a way the run of
its function ends. -/
def Ev.dropLeft : Ev (Except Stuck (Result (α × Nat))) → Ev (Except Stuck (Result α))
  | .ok (.ok (.ret (a, _))) => .ok (.ok (.ret a))
  | .ok (.ok .fuelExhausted) => .ok (.ok .fuelExhausted)
  | .ok (.error st) => .ok (.error st)
  | .ub r => .ub r

/-- A run of a function ends as its entry block's ops end, or stuck where
it cannot start. -/
theorem Func.run_run (M : Module d) (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (n : Nat) (e : Ev (Except Stuck (Result (List (DVal d))))) :
    (f.run M (m := SetM) args n).run e ↔
      (∃ p, f.enter args.toDVals = .ok p ∧
        ∃ e', (Func.runOps (m := SetM) M n f p.2 p.1).run e' ∧ e = e'.dropLeft) ∨
      (∃ st, f.enter args.toDVals = .error st ∧ e = .ok (.error st)) := by
  simp only [Func.run]
  rw [run_bind]
  cases hen : f.enter args.toDVals with
  | error st =>
    simp only [run_liftExcept]
    constructor
    · rintro (⟨_, h, _⟩ | ⟨st', h, rfl⟩ | ⟨_, h, _⟩)
      · cases h
      · cases h; exact .inr ⟨_, rfl, rfl⟩
      · cases h
    · rintro (⟨_, h, _⟩ | ⟨_, h, rfl⟩)
      · cases h
      · cases h; exact .inr (.inl ⟨_, rfl, rfl⟩)
  | ok p =>
    simp only [run_liftExcept]
    constructor
    · rintro (⟨p', h, hr⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩)
      · cases h
        refine .inl ⟨_, rfl, ?_⟩
        rcases (run_bind _ _ _).1 hr with ⟨r, hr, he⟩ | ⟨st, hst, rfl⟩ | ⟨u, hu, rfl⟩
        · match r, hr, he with
          | .ret (vs, k), hr, he => exact ⟨_, hr, (run_pure _ _).1 he⟩
          | .fuelExhausted, hr, he => exact ⟨_, hr, (run_pure _ _).1 he⟩
        · exact ⟨_, hst, rfl⟩
        · exact ⟨_, hu, rfl⟩
      · cases h
      · cases h
    · rintro (⟨p', h, e', he', rfl⟩ | ⟨_, h, _⟩)
      · cases h
        refine .inl ⟨_, rfl, (run_bind _ _ _).2 ?_⟩
        match e', he' with
        | .ok (.ok (.ret (vs, k))), he' => exact .inl ⟨_, he', rfl⟩
        | .ok (.ok .fuelExhausted), he' => exact .inl ⟨_, he', rfl⟩
        | .ok (.error st), he' => exact .inr (.inl ⟨st, he', rfl⟩)
        | .ub r, he' => exact .inr (.inr ⟨r, he', rfl⟩)
      · cases h

/-- A run of a function with `j` more steps of fuel: each return or UB of
the smaller run is one of the larger. -/
theorem Func.run_up (M : Module d) (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (n j : Nat) (e : Ev (Except Stuck (Result (List (DVal d)))))
    (hne : e ≠ .ok (.ok .fuelExhausted)) (hst : ∀ st, e ≠ .ok (.error st))
    (hs : (f.run M (m := SetM) args n).run e) : (f.run M (m := SetM) args (n + j)).run e := by
  rcases (Func.run_run M f args n e).1 hs with ⟨p, hp, e', he', rfl⟩ | ⟨st, _, he⟩
  · have ha := Func.runOps_ahead M n j f p.2 p.1
    refine (Func.run_run M f args (n + j) _).2 (.inl ⟨p, hp, ?_⟩)
    match e', he' with
    | .ok (.ok (.ret (_, k))), he' => exact ⟨_, ha.up_ret _ k he', rfl⟩
    | .ub _, he' => exact ⟨_, ha.up_ub _ he', rfl⟩
    | .ok (.ok .fuelExhausted), _ => exact absurd rfl hne
    | .ok (.error st), _ => exact absurd rfl (hst st)
  · exact absurd he (hst st)

/-- A run of a function with `j` more steps of fuel: each return or UB of
the larger run is one of the smaller, unless the smaller can run out of
fuel. -/
theorem Func.run_down (M : Module d) (f : Func d) (args : HVector toType (f.params.map (·.2)))
    (n j : Nat) (e : Ev (Except Stuck (Result (List (DVal d)))))
    (hne : e ≠ .ok (.ok .fuelExhausted)) (hst : ∀ st, e ≠ .ok (.error st))
    (ht : (f.run M (m := SetM) args (n + j)).run e) :
    (f.run M (m := SetM) args n).run e ∨ (f.run M (m := SetM) args n).run (.ok (.ok .fuelExhausted)) := by
  rcases (Func.run_run M f args (n + j) e).1 ht with ⟨p, hp, e', he', rfl⟩ | ⟨st, _, he⟩
  · have ha := Func.runOps_ahead M n j f p.2 p.1
    have back : ∀ e'', (Func.runOps (m := SetM) M n f p.2 p.1).run e'' →
        (f.run M (m := SetM) args n).run e''.dropLeft :=
      fun e'' h => (Func.run_run M f args n _).2 (.inl ⟨p, hp, e'', h, rfl⟩)
    match e', he' with
    | .ok (.ok (.ret (_, k))), he' =>
      rcases ha.down_ret _ k he' with ⟨_, hs⟩ | hs
      · exact .inl (back (.ok (.ok (.ret (_, k - j)))) hs)
      · exact .inr (back _ hs)
    | .ub _, he' =>
      rcases ha.down_ub _ he' with hs | hs
      · exact .inl (back _ hs)
      · exact .inr (back _ hs)
    | .ok (.ok .fuelExhausted), _ => exact absurd rfl hne
    | .ok (.error st), _ => exact absurd rfl (hst st)
  · exact absurd he (hst st)

/-- The runs of every function of every module are fuel-monotone, calls
included, whatever its ops do. -/
theorem Func.fuelMonotone (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.runs M args) where
  up {n m o} hnm ho hs := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    cases o with
    | ret a => exact Func.run_up M f args n j _ (fun h => nomatch h) (fun _ h => nomatch h) hs
    | ub r => exact Func.run_up M f args n j _ (fun h => nomatch h) (fun _ h => nomatch h) hs
    | fuelExhausted => exact absurd rfl ho
  down {n m o} hnm ho ht := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    cases o with
    | ret a => exact Func.run_down M f args n j _ (fun h => nomatch h) (fun _ h => nomatch h) ht
    | ub r => exact Func.run_down M f args n j _ (fun h => nomatch h) (fun _ h => nomatch h) ht
    | fuelExhausted => exact absurd rfl ho

end Fir
