import Fir.Execution.MemoryStepPaths
import Fir.Execution.BlackBox
import Fir.Memory.Refine

/-!
# Runs of a function from given memories

A run with memory starts from the empty memories, and an observer sees what
it returns (the section on runs with memory). A call is a run of its callee
too, but from the memories that its caller reached, and its caller goes on
from the memories that the callee leaves. So refinement through calls with
memory compares the runs of a function _from given memories_, and what they
return with the memories they end with: an observation of a run from given
memories is the values it returns and the memories it ends with, and one
refines another when the values refine the other's and the memories refine
the other's.

Such a run is its entry block's ops run in a frame, as every call's callee
is, with what they return finished:

* it returns what its entry block's ops return, with the memories they end
  with, the frame left; it runs out of fuel when they do; it hits UB when
  they do;
* it is fuel-monotone, as the runs with memory are;
* the runs with memory of a function are its runs from the empty memories,
  with the memories they end with dropped. So when its runs from the empty
  memories refine others', so do its runs with memory.

A run in a call's frame with more fuel is ahead of the run with less, from
the same memories, as the run in the frame's ops is, and gives back at most
the fuel it was given. A run that runs out of fuel runs out of fuel with
fewer steps too.
-/

namespace Fir

open SetM Memory

variable {α β : Type}

/-- A way a function's run ends, read from given memories with the memories
it ends with: a return carries them, and a run out of fuel shows none. -/
def Result.withMem {σ : Type} : Result α × σ → Result (α × σ)
  | (.ret a, S) => .ret (a, S)
  | (.fuelExhausted, _) => .fuelExhausted

/-- A path of a run of ops, finished, is a path of the run of ops without
the steps it leaves. -/
theorem Result.finish_id_run {X : ExceptT Stuck SetM (Result (α × Nat))}
    {e : Ev (Except Stuck (Result α))} :
    (Result.finish id X).run e ↔ ∃ e', X.run e' ∧ e = e'.dropLeft := by
  unfold Result.finish
  rw [run_bind]
  constructor
  · rintro (⟨r, hr, h⟩ | ⟨st, hst, rfl⟩ | ⟨u, hu, rfl⟩)
    · match r, hr, h with
      | .ret (a, k), hr, h => exact ⟨_, hr, (run_pure _ _).1 h⟩
      | .fuelExhausted, hr, h => exact ⟨_, hr, (run_pure _ _).1 h⟩
    · exact ⟨_, hst, rfl⟩
    · exact ⟨_, hu, rfl⟩
  · rintro ⟨e', he', rfl⟩
    match e', he' with
    | .ok (.ok (.ret (a, k))), he' => exact .inl ⟨_, he', rfl⟩
    | .ok (.ok .fuelExhausted), he' => exact .inl ⟨_, he', rfl⟩
    | .ok (.error st), he' => exact .inr (.inl ⟨st, he', rfl⟩)
    | .ub r, he' => exact .inr (.inr ⟨r, he', rfl⟩)

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]

/-! # A run in a call's frame -/

/-- A run in a call's frame is the run of its ops from the memories with a
new frame entered, each return leaving the frame. -/
theorem Func.memCall_eq (M : Module d) (n : Nat) (g : Func d) (genv : Env d)
    (body : List (Operation d)) (S : Memories Mem unit) :
    Func.memCall M n g genv body S =
      Result.mapVal (fun p : List (DVal d) × Memories Mem unit => (p.1, p.2.exit)) <$>
        Func.memOps M n g genv body S.enter :=
  runFrom_inFrame _ S

/-- A run in a call's frame with `j` more steps of fuel is ahead of the run
with fewer, from the same memories. -/
theorem Func.memCall_ahead (M : Module d) (n j : Nat) (g : Func d) (genv : Env d)
    (body : List (Operation d)) (S : Memories Mem unit) :
    Ahead j (Func.memCall M n g genv body S) (Func.memCall M (n + j) g genv body S) := by
  rw [Func.memCall_eq, Func.memCall_eq]
  exact (Func.runOps_memAhead M n j g genv body S.enter).mapVal _

/-- A run in a call's frame gives back at most the steps of fuel it was
given. -/
theorem Func.memCall_left_le (M : Module d) (n : Nat) (g : Func d) (genv : Env d)
    (body : List (Operation d)) (S : Memories Mem unit) :
    LeavesAtMost n (Func.memCall M n g genv body S) := by
  rw [Func.memCall_eq]
  exact (Func.runOps_memLeft_le M n g genv body S.enter).mapVal _

/-- A run with memory that runs out of fuel with `j` more steps runs out of
fuel with fewer, from the same memories: it takes the same path, and runs
out sooner. -/
theorem Func.memOps_exhausted_down (M : Module d) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)) (S : Memories Mem unit),
      (Func.memOps M (n + j) f env os S).run (.ok (.ok .fuelExhausted)) →
      (Func.memOps M n f env os S).run (.ok (.ok .fuelExhausted)) := by
  have hne : Ev.NotStuck (.ok (.ok .fuelExhausted) :
      Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))) :=
    fun _ h => nomatch h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os S h
    match n, os with
    | 0, _ => exact Func.run_memOps_zero.2 rfl
    | k + 1, [] => rw [Nat.add_right_comm] at h; exact absurd h (Func.run_memOps_nil hne)
    | k + 1, o :: os =>
      rw [Nat.add_right_comm] at h
      refine (Func.memStepPath_iff hne).2 ?_
      have exhCall : ∀ {g genv body}, (Func.memCall M (k + j) g genv body S).run
          (.ok (.ok .fuelExhausted)) → (Func.memCall M k g genv body S).run (.ok (.ok .fuelExhausted)) :=
        fun hx => by
          rw [Func.memCall_eq] at hx ⊢
          rcases (SetM.run_map _ _ _).1 hx with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
          · match r, hr, he with
            | .fuelExhausted, hr, _ =>
              exact (SetM.run_map _ _ _).2 (.inl ⟨_, ih k (Nat.lt_succ_self k) j _ _ _ _ hr, rfl⟩)
            | .ret _, _, he => cases he
          · cases he
          · cases he
      cases (Func.memStepPath_iff hne).1 h with
      | goto hreg hargs hT hos hx hj h =>
        exact .goto hreg hargs hT hos hx hj (ih k (Nat.lt_succ_self k) j _ _ _ _ h)
      | denote hreg hargs hT hc hx hlen h =>
        exact .denote hreg hargs hT hc hx hlen (ih k (Nat.lt_succ_self k) j _ _ _ _ h)
      | callExh hreg hargs hT hc hg hen hx => exact .callExh hreg hargs hT hc hg hen (exhCall hx)
      | callRet hreg hargs hT hc hg hen hx hty hlen h =>
        rename_i vs S' kk
        have hle := Func.memCall_left_le M (k + j) _ _ _ _ _ _ hx
        rcases (Func.memCall_ahead M k j _ _ _ _).down_ret _ kk hx with ⟨hj, hx'⟩ | hx'
        · have hle' : kk - j ≤ k := by omega
          have hmin : min kk (k + j) = (kk - j) + j := by omega
          rw [hmin] at h
          have h' := ih (kk - j) (Nat.lt_succ_of_le hle') j _ _ _ _ h
          refine .callRet hreg hargs hT hc hg hen hx' hty hlen ?_
          rwa [Nat.min_eq_left hle']
        · exact .callExh hreg hargs hT hc hg hen hx'

/-! # Runs of a function from given memories -/

/-- The runs of the function `f` of the module `M` from given memories: on
each argument vector and from each memories, its run with memory at each
budget, which returns its values with the memories it ends with. -/
def Func.memRunsFrom (M : Module d) (f : Func d) :
    FuncRuns (HVector toType (f.params.map (·.2)) × Memories Mem unit)
      (List (DVal d) × Memories Mem unit) :=
  fun p n => (Result.withMem <$> fromState (f.run M (m := StateT (Memories Mem unit) SetM) p.1 n) p.2 :
    ExceptT Stuck SetM (Result (List (DVal d) × Memories Mem unit)))

/-- A run of a function from given memories that starts is its entry
block's ops run in a frame, finished. -/
theorem Func.memRunsFrom_enter (M : Module d) (f : Func d)
    (a : HVector toType (f.params.map (·.2))) (S : Memories Mem unit) (n : Nat)
    {body : List (Operation d)} {env : Env d} (hen : f.enter a.toDVals = .ok (body, env)) :
    f.memRunsFrom M (a, S) n = Result.finish id (Func.memCall M n f env body S) := by
  simp only [Func.memRunsFrom, Func.run_of_enter M f a n hen, fromState_bind, map_bind, Result.finish, Func.memCall, runFrom,
    bind_map_left]
  refine congrArg (fromState _ S >>= ·) (funext fun q => ?_)
  obtain ⟨r, S'⟩ := q
  cases r with
  | ret p => simp only [fromState_pure, map_pure]; rfl
  | fuelExhausted => simp only [fromState_pure, map_pure]; rfl

/-- A path of a function's run from given memories that is not stuck is a
path of its entry block's ops in a frame, from those memories, without the
steps it leaves; and each such path is one of the function's run. -/
theorem Func.memRunsFrom_run {M : Module d} {f : Func d} {a : HVector toType (f.params.map (·.2))}
    {S : Memories Mem unit} {n : Nat} {x : Ev (Except Stuck (Result (List (DVal d) × Memories Mem unit)))}
    (hne : Ev.NotStuck x) :
    (f.memRunsFrom M (a, S) n) x ↔
      ∃ p, f.enter a.toDVals = .ok p ∧ ∃ e, (Func.memCall M n f p.2 p.1 S).run e ∧ x = e.dropLeft := by
  cases hen : f.enter a.toDVals with
  | error st =>
    refine ⟨fun h => ?_, fun ⟨_, h, _⟩ => nomatch h⟩
    have hx := fun {e'} => Func.fromState_run_stuck M f a n S hen (e := e')
    rcases (SetM.run_map _ _ _).1 h with ⟨_, h1, -⟩ | ⟨_, h1, rfl⟩ | ⟨_, h1, -⟩
    · cases hx h1
    · exact absurd rfl (hne _)
    · cases hx h1
  | ok p =>
    obtain ⟨body, env⟩ := p
    rw [Func.memRunsFrom_enter M f a S n hen]
    refine Result.finish_id_run.trans ?_
    exact ⟨fun ⟨e, he, hx⟩ => ⟨_, rfl, e, he, hx⟩, fun ⟨_, h, e, he, hx⟩ => by cases h; exact ⟨e, he, hx⟩⟩

/-- The runs of every function from given memories are fuel-monotone. -/
theorem Func.memRunsFrom_fuelMonotone (M : Module d) (f : Func d)
    (a : HVector toType (f.params.map (·.2))) (S : Memories Mem unit) :
    FuelMonotone (f.memRunsFrom M (a, S)) := by
  have up : ∀ n j e, e ≠ .ok (.ok .fuelExhausted) → (∀ st, e ≠ .ok (.error st)) →
      f.memRunsFrom M (a, S) n e → f.memRunsFrom M (a, S) (n + j) e := by
    intro n j e hne hst hs
    obtain ⟨⟨body, env⟩, hen, -⟩ := (Func.memRunsFrom_run hst).1 hs
    rw [Func.memRunsFrom_enter M f a S _ hen] at hs ⊢
    exact (Func.memCall_ahead M n j f env body S).finish_up id hne hst hs
  have down : ∀ n j e, e ≠ .ok (.ok .fuelExhausted) → (∀ st, e ≠ .ok (.error st)) →
      f.memRunsFrom M (a, S) (n + j) e →
      f.memRunsFrom M (a, S) n e ∨ f.memRunsFrom M (a, S) n (.ok (.ok .fuelExhausted)) := by
    intro n j e hne hst ht
    obtain ⟨⟨body, env⟩, hen, -⟩ := (Func.memRunsFrom_run hst).1 ht
    rw [Func.memRunsFrom_enter M f a S _ hen] at ht ⊢
    exact (Func.memCall_ahead M n j f env body S).finish_down id hne hst ht
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

/-- A function's run from given memories that runs out of fuel runs out of
fuel with fewer steps. -/
theorem Func.memRunsFrom_exhausted_down {M : Module d} {f : Func d}
    {a : HVector toType (f.params.map (·.2))} {S : Memories Mem unit} {n m : Nat} (h : n ≤ m)
    (hm : (f.memRunsFrom M (a, S) m).outcomes .fuelExhausted) :
    (f.memRunsFrom M (a, S) n).outcomes .fuelExhausted := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨p, hp, e, he, hx⟩ :=
    (Func.memRunsFrom_run (x := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h)).1 hm
  match e, he, hx with
  | .ok (.ok (.ret _)), _, hx | .ub _, _, hx | .ok (.error _), _, hx => cases hx
  | .ok (.ok .fuelExhausted), he, _ =>
    refine (Func.memRunsFrom_run (x := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h)).2
      ⟨p, hp, .ok (.ok .fuelExhausted), ?_, rfl⟩
    rw [Func.memCall_eq] at he ⊢
    rcases (SetM.run_map _ _ _).1 he with ⟨r, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · match r, hr, he with
      | .fuelExhausted, hr, _ =>
        exact (SetM.run_map _ _ _).2 (.inl ⟨_, Func.memOps_exhausted_down M n j _ _ _ _ hr, rfl⟩)
      | .ret _, _, he => cases he
    · cases he
    · cases he

end

/-! # Runs with memory, from the empty memories -/

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] [TyRefinement d.Ty] {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)

/-- The runs with memory of a function refine those of another when their
runs from the empty memories do: they are those runs, with the memories they
end with dropped. -/
theorem Func.memRuns_isRefinedBy_of_from {M M' : Module d} {f f' : Func d}
    {a : HVector toType (f.params.map (·.2))} {a' : HVector toType (f'.params.map (·.2))}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      observable (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay)))) ⊑
        observable (f'.memRunsFrom M' (a', (Memories.empty : Memories N (unitsOf lay))))) :
    observable (f.memRuns lay ρ M a) ⊑ observable (f'.memRuns lay ρ M' a') := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  have hX : ∀ {g : Func d} {L : Module d} {b : HVector toType (g.params.map (·.2))} {n : Nat},
      g.memRuns lay ρ L b n = (Prod.fst <$> fromState
        (g.run L (m := StateT (Memories N (unitsOf lay)) SetM) b n) Memories.empty).run :=
    fromState_fst _ _
  have kret : ∀ {g : Func d} {L : Module d} {b : HVector toType (g.params.map (·.2))} {n : Nat}
      {vs : List (DVal d)}, (g.memRuns lay ρ L b n).outcomes (.ret vs) ↔
        ∃ T, (g.memRunsFrom L (b, (Memories.empty : Memories N (unitsOf lay))) n).outcomes (.ret
            (vs, T)) := by
    intro g L b n vs
    simp only [Run.outcomes, Func.memRunsFrom, hX]
    constructor
    · intro h
      rcases (SetM.run_map _ _ _).1 h with ⟨⟨r, T⟩, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
      · cases he
        exact ⟨T, (SetM.run_map _ _ _).2 (.inl ⟨_, hr, rfl⟩)⟩
      · cases he
      · cases he
    · rintro ⟨T, h⟩
      rcases (SetM.run_map _ _ _).1 h with ⟨⟨r, T'⟩, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
      · cases r with
        | ret _ => cases he; exact (SetM.run_map _ _ _).2 (.inl ⟨_, hr, rfl⟩)
        | fuelExhausted => cases he
      · cases he
      · cases he
  have kub : ∀ {g : Func d} {L : Module d} {b : HVector toType (g.params.map (·.2))} {n : Nat}
      {r : String}, (g.memRuns lay ρ L b n).outcomes (.ub r) ↔
        (g.memRunsFrom L (b, (Memories.empty : Memories N (unitsOf lay))) n).outcomes (.ub r) := by
    intro g L b n r
    simp only [Run.outcomes, Func.memRunsFrom, hX]
    constructor
    · intro h
      rcases (SetM.run_map _ _ _).1 h with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, hr, he⟩
      · cases he
      · cases he
      · cases he
        exact (SetM.run_map _ _ _).2 (.inr (.inr ⟨_, hr, rfl⟩))
    · intro h
      rcases (SetM.run_map _ _ _).1 h with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, hr, he⟩
      · cases he
      · cases he
      · cases he
        exact (SetM.run_map _ _ _).2 (.inr (.inr ⟨_, hr, rfl⟩))
  have kexh : ∀ {g : Func d} {L : Module d} {b : HVector toType (g.params.map (·.2))} {n : Nat},
      (g.memRuns lay ρ L b n).outcomes .fuelExhausted ↔
        (g.memRunsFrom L (b, (Memories.empty : Memories N (unitsOf lay)))
            n).outcomes .fuelExhausted := by
    intro g L b n
    simp only [Run.outcomes, Func.memRunsFrom, hX]
    constructor
    · intro h
      rcases (SetM.run_map _ _ _).1 h with ⟨⟨r, T⟩, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
      · cases r with
        | ret _ => cases he
        | fuelExhausted => exact (SetM.run_map _ _ _).2 (.inl ⟨_, hr, rfl⟩)
      · cases he
      · cases he
    · intro h
      rcases (SetM.run_map _ _ _).1 h with ⟨⟨r, T⟩, hr, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
      · cases r with
        | ret _ => cases he
        | fuelExhausted => exact (SetM.run_map _ _ _).2 (.inl ⟨_, hr, rfl⟩)
      · cases he
      · cases he
  intro t ht
  match t, ht with
  | .ret vs', ⟨n, hn⟩ =>
    obtain ⟨T', h₀⟩ := kret.1 hn
    obtain ⟨s, hs, hle⟩ := h (.ret (vs', T')) ⟨n, h₀⟩
    match s, hs, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ⟨.ub r, ⟨N, kub.2 hN⟩, trivial⟩
    | .ret (vs, T), ⟨N, hN⟩, hle => exact ⟨.ret vs, ⟨N, kret.2 ⟨T, hN⟩⟩, hle.1⟩
    | .fuelExhausted, _, hle => exact hle.elim
  | .ub r', ⟨n, hn⟩ =>
    obtain ⟨s, hs, hle⟩ := h (.ub r') ⟨n, kub.1 hn⟩
    match s, hs, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ⟨.ub r, ⟨N, kub.2 hN⟩, trivial⟩
    | .ret _, _, hle | .fuelExhausted, _, hle => exact hle.elim
  | .fuelExhausted, ht =>
    obtain ⟨s, hs, hle⟩ := h .fuelExhausted fun n => kexh.1 (ht n)
    match s, hs, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ⟨.ub r, ⟨N, kub.2 hN⟩, trivial⟩
    | .fuelExhausted, hs, _ => exact ⟨.fuelExhausted, fun N => kexh.2 (hs N), trivial⟩
    | .ret _, _, hle => exact hle.elim

end

end Fir
