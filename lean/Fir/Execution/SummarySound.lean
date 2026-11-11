import Fir.Execution.SummaryFixpoint
import Fir.Execution.EffectLaws
import Fir.Execution.Lawful

/-!
# Function summaries are sound

A pass may rely on a function's summary as it relies on an op's effects,
because the summary is proved sound: an effect that it leaves out, a run
of the function does not have (ADR-2026-11-10-2108). In a dialect lawful in
its effects, for a function of a module whose functions are all valid:

* _No may-UB_: when its summary leaves out may-UB, no run of the function
  ends in UB, at any budget of fuel.
* _No may produce poison_: when its summary leaves out may produce poison,
  a run of the function on arguments with no poison returns no poison
  (ADR-2026-11-09-2249).

The proofs follow a run op by op, by induction on its fuel, as the proofs
of progress with calls do. Each op that runs by its own rule leaves out
each effect that its function's summary leaves out, and so does every
function it calls; each callee runs with less fuel, so the induction covers
its run, recursion included.

* An op that runs by its own rule, a terminator or an op with no callee,
  is covered by the obligations of a dialect lawful in its effects: it
  never ends in UB, and gives no poison on operands with no poison.
* A call runs its callee, whose summary is below its caller's, so it leaves
  out the effects that its caller's leaves out.
* For poison, the run keeps an environment with no poison: the arguments
  have none, the operands that it finds there have none, so neither do the
  results that an op gives, the values that a jump passes, the arguments
  of a callee, or the values that a callee returns.
-/

namespace Fir

open SetM

/-! # Values with no poison -/

section Clean

variable {d : Dialect} [TyDenote d.Ty] [TyPoison d.Ty]

/-- No value of a list is poison. -/
def DVals.Clean (vs : List (DVal d)) : Prop := ∀ v ∈ vs, ¬ TyPoison.IsPoison v.2

/-- No value that an environment binds is poison. -/
def Env.Clean (env : Env d) : Prop := ∀ p ∈ env, ¬ TyPoison.IsPoison p.2.2

/-- The values of a vector have no poison when no element of it is poison. -/
theorem HVector.clean_toDVals : ∀ {ts : List d.Ty} (xs : HVector toType ts),
    DVals.Clean xs.toDVals ↔ ¬ xs.Any TyPoison.IsPoison
  | [], .nil => ⟨fun _ h => h, fun _ _ h => nomatch h⟩
  | _ :: _, .cons x xs => by
    simp only [DVals.Clean, HVector.toDVals, List.mem_cons, forall_eq_or_imp, HVector.Any,
      not_or]
    exact and_congr Iff.rfl (HVector.clean_toDVals xs)

/-- A name that a list looks up is bound in it. -/
theorem mem_of_lookup {β : Type} {x : Name} {v : β} :
    ∀ {l : List (Name × β)}, l.lookup x = some v → (x, v) ∈ l
  | (y, u) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hxy
      cases h
      rw [beq_iff_eq.1 hxy]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- A value that an environment with no poison binds is not poison. -/
theorem Env.Clean.value {env : Env d} (h : env.Clean) {x : Name} {v : DVal d}
    (hv : env.value x = .ok v) : ¬ TyPoison.IsPoison v.2 := by
  simp only [Env.value] at hv
  split at hv
  · rename_i v' hl
    cases hv
    exact h _ (mem_of_lookup hl)
  · cases hv

/-- Binding values with no poison in an environment with none leaves none. -/
theorem Env.Clean.bind {env : Env d} (h : env.Clean) (names : List Name) {vs : List (DVal d)}
    (hvs : DVals.Clean vs) : Env.Clean (names.zip vs ++ env) := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · exact hvs _ (List.of_mem_zip hp).2
  · exact h p hp

/-- The values found in an environment with no poison have none. -/
theorem Env.Clean.mapM_value {env : Env d} (h : env.Clean) :
    ∀ {xs : List Name} {vs : List (DVal d)}, xs.mapM env.value = .ok vs → DVals.Clean vs
  | [], _, hm => by cases hm; exact fun _ h => nomatch h
  | x :: xs, vs, hm => by
    simp only [List.mapM_cons] at hm
    cases hx : env.value x with
    | error e => rw [hx] at hm; cases hm
    | ok v =>
      cases hxs : xs.mapM env.value with
      | error e => rw [hx, hxs] at hm; cases hm
      | ok vs' =>
        rw [hx, hxs] at hm
        cases hm
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact h.value hx
        · exact h.mapM_value hxs w hw

variable [DecidableEq d.Ty]

/-- The operands found in an environment with no poison have none. -/
theorem Env.Clean.operands {env : Env d} (h : env.Clean) :
    ∀ {ts : List d.Ty} {xs : List Name} {args : HVector toType ts},
      env.operands ts xs = .ok args → ¬ args.Any TyPoison.IsPoison
  | [], [], .nil, _ => fun h => h
  | t :: ts, x :: xs, _, hm => by
    obtain ⟨v, as, hx, hxs, rfl⟩ := Env.operands_cons_ok.1 hm
    rintro (hp | hp)
    · exact h.value hx hp
    · exact h.operands hxs hp
  | [], _ :: _, _, hm | _ :: _, [], _, hm => by cases hm

end Clean

/-! # Runs -/

variable {d : Dialect}

/-- An op of a block of a function is one of its ops at any depth. -/
theorem Func.mem_allOps {f : Func d} {b : Block d} (hb : b ∈ f.blocks) {o : Operation d}
    (ho : o ∈ b.body) : o ∈ f.allOps :=
  List.mem_flatMap.2 ⟨b, Block.mem_allBlocks hb, ho⟩

/-- The ops that a function starts its run with are ops of its blocks. -/
theorem Func.enter_ops [TyDenote d.Ty] [DecidableEq d.Ty] {g : Func d} {dvs : List (DVal d)}
    {body : List (Operation d)} {genv : Env d} (h : g.enter dvs = .ok (body, genv)) :
    (∀ o ∈ body, ∃ b ∈ g.blocks, o ∈ b.body) ∧ genv = (g.params.map (·.1)).zip dvs := by
  obtain ⟨e, he, -, -, hp⟩ := Func.enter_eq_ok h
  cases hp
  exact ⟨fun o ho => ⟨e, List.mem_of_mem_head? he, ho⟩, rfl⟩

variable [DialectSignature d] [DialectCall d]

/-- An op that is not a terminator calls its callee. -/
theorem Operation.call?_of {o : Operation d} {c : Name} (hT : isTerminator o.op = false)
    (hc : callee? o.op = some c) : o.call? = some c := by
  simp [Operation.call?, hT, hc]

variable [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty] [DialectDenote d SetM]
  [DialectEffects d] [DialectValidation d] [DialectMemDenote d] [LawfulDialectEffects d]
  {ctx : ModuleContext d} {M : Module d}

/-- No run of ops of a function of `M` ends in UB when the function's
summary leaves out may-UB, from any of its ops on, at any budget. -/
theorem Module.runOps_notUB (hv : ∀ g ∈ M.funcs, g.Valid ctx) (n : Nat) :
    ∀ (s : Name) (f : Func d) (env : Env d) (os : List (Operation d)) (r : String),
      M.func? s = some f → (M.table.summary s).mayUB = false →
      (∀ o ∈ os, ∃ b ∈ f.blocks, o ∈ b.body) →
      ¬ (Func.runOps (m := SetM) M n f env os).run (.ub r) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s f env os r hf hs hos h
  have hfm : f ∈ M.funcs := List.mem_of_find?_eq_some hf
  cases n with
  | zero => simp only [Func.runOps] at h; cases (run_pure _ _).1 h
  | succ n =>
  cases os with
  | nil => simp only [Func.runOps] at h; cases (run_liftExcept _ _).1 h
  | cons o os =>
  obtain ⟨b, hb, ho⟩ := hos o List.mem_cons_self
  have htv := (hv f hfm).typesValid hb ho
  have hown : (effects o.op).mayUB = false := by
    cases he : (effects o.op).mayUB
    · rfl
    · exact absurd ((M.table.effects_le_summary hf (Func.mem_allOps hb ho)).mayUB he) (by simp [hs])
  have htail : ∀ o' ∈ os, ∃ b ∈ f.blocks, o' ∈ b.body :=
    fun o' h' => hos o' (List.mem_cons_of_mem _ h')
  rw [Func.stepPath_iff (by intro _ h; cases h)] at h
  cases h with
  | exitUB _ _ hT _ hx =>
    exact (LawfulDialectEffects.neverUB o.op htv (.inl hT) hown _ r).2 hT hx
  | goto _ _ _ _ _ hj hrun =>
    obtain ⟨_, _, _, hblk, -⟩ := Func.jump_eq_ok hj
    exact ih n (Nat.lt_succ_self n) s f _ _ r hf hs
      (fun o' h' => ⟨_, (Func.block?_some hblk).1, h'⟩) hrun
  | denoteUB _ _ hT hc hx =>
    exact (LawfulDialectEffects.neverUB o.op htv (.inr hc) hown _ r).1 hT hx
  | denote _ _ _ _ _ _ hrun => exact ih n (Nat.lt_succ_self n) s f _ os r hf hs htail hrun
  | @callUB _ c g _ _ _ _ _ hT hc hg hen hx =>
    have hg' : M.table.func? c = some g := hg
    have hcs : (M.table.summary c).mayUB = false := by
      cases he : (M.table.summary c).mayUB
      · rfl
      · exact absurd ((M.table.summary_closed.calls s f hf o (Func.mem_allOps hb ho) c
          (Operation.call?_of hT hc) (by simp [hg'])).mayUB he) (by simp [hs])
    exact ih n (Nat.lt_succ_self n) c g _ _ r hg hcs (Func.enter_ops hen).1 hx
  | callRet _ _ _ _ _ _ _ _ _ hrun =>
    exact ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) s f _ os r hf hs htail hrun

/-- A run of ops of a function of `M` returns no poison when the function's
summary leaves out may produce poison and its environment has none, from
any of its ops on, at any budget. -/
theorem Module.runOps_clean (hv : ∀ g ∈ M.funcs, g.Valid ctx) (n : Nat) :
    ∀ (s : Name) (f : Func d) (env : Env d) (os : List (Operation d)) (vs : List (DVal d))
      (k : Nat), M.func? s = some f → (M.table.summary s).mayPoison = false → env.Clean →
      (∀ o ∈ os, ∃ b ∈ f.blocks, o ∈ b.body) →
      (Func.runOps (m := SetM) M n f env os).run (.ok (.ok (.ret (vs, k)))) → DVals.Clean vs := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s f env os vs k hf hs henv hos h
  have hfm : f ∈ M.funcs := List.mem_of_find?_eq_some hf
  cases n with
  | zero => simp only [Func.runOps] at h; cases (run_pure _ _).1 h
  | succ n =>
  cases os with
  | nil => simp only [Func.runOps] at h; cases (run_liftExcept _ _).1 h
  | cons o os =>
  obtain ⟨b, hb, ho⟩ := hos o List.mem_cons_self
  have htv := (hv f hfm).typesValid hb ho
  have hown : (effects o.op).mayPoison = false := by
    cases he : (effects o.op).mayPoison
    · rfl
    · exact absurd ((M.table.effects_le_summary hf (Func.mem_allOps hb ho)).mayPoison he)
        (by simp [hs])
  have htail : ∀ o' ∈ os, ∃ b ∈ f.blocks, o' ∈ b.body :=
    fun o' h' => hos o' (List.mem_cons_of_mem _ h')
  rw [Func.stepPath_iff (by intro _ h; cases h)] at h
  cases h with
  | ret _ hargs _ _ _ _ => exact (HVector.clean_toDVals _).2 (henv.operands hargs)
  | goto _ _ _ _ _ hj hrun =>
    obtain ⟨_, vs', _, hblk, hvs, -, -, rfl⟩ := Func.jump_eq_ok hj
    exact ih n (Nat.lt_succ_self n) s f _ _ vs k hf hs (henv.bind _ (henv.mapM_value hvs))
      (fun o' h' => ⟨_, (Func.block?_some hblk).1, h'⟩) hrun
  | @denote args rs _ _ hargs hT hc hx _ hrun =>
    have hrs := LawfulDialectEffects.makesNoPoison o.op htv (.inr hc) hown hT args
      (henv.operands hargs) rs hx
    exact ih n (Nat.lt_succ_self n) s f _ os vs k hf hs
      (henv.bind _ ((HVector.clean_toDVals rs).2 hrs)) htail hrun
  | @callRet args c g _ _ vs' k' _ _ hargs hT hc hg hen hcallee _ _ hrun =>
    have hg' : M.table.func? c = some g := hg
    have hcs : (M.table.summary c).mayPoison = false := by
      cases he : (M.table.summary c).mayPoison
      · rfl
      · exact absurd ((M.table.summary_closed.calls s f hf o (Func.mem_allOps hb ho) c
          (Operation.call?_of hT hc) (by simp [hg'])).mayPoison he) (by simp [hs])
    obtain ⟨hops, rfl⟩ := Func.enter_ops hen
    have hgenv : Env.Clean ((g.params.map (·.1)).zip args.toDVals) := by
      simpa using (show Env.Clean ([] : Env d) from fun _ h => nomatch h).bind
        (g.params.map (·.1)) ((HVector.clean_toDVals args).2 (henv.operands hargs))
    have hvs' := ih n (Nat.lt_succ_self n) c g _ _ vs' k' hg hcs hgenv hops hcallee
    exact ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) s f _ os vs k hf hs
      (henv.bind _ hvs') htail hrun

/-- No run of a function of `M` ends in UB when its summary leaves out
may-UB, at any budget of fuel, when every function of `M` is valid and
the dialect is lawful in its effects. -/
theorem Module.summary_neverUB (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d}
    (hf : M.func? s = some f) (hs : (M.table.summary s).mayUB = false)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (r : String) :
    ¬ (f.run (m := SetM) M args fuel).run (.ub r) := by
  intro h
  simp only [Func.run] at h
  obtain ⟨⟨body, env⟩, hen, h⟩ := (run_liftExcept_bind (by intro _ h; cases h)).1 h
  rcases (run_bind _ _ _).1 h with ⟨x, _, h⟩ | ⟨_, _, he⟩ | ⟨_, hr, he⟩
  · rcases x with ⟨_, _⟩ | _ <;> cases (run_pure _ _).1 h
  · cases he
  · cases he
    exact Module.runOps_notUB hv fuel s f env body r hf hs (Func.enter_ops hen).1 hr

/-- A run of a function of `M` on arguments with no poison returns no
poison when its summary leaves out may produce poison, at any budget of
fuel, when every function of `M` is valid and the dialect is lawful in its
effects. -/
theorem Module.summary_noPoison (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d}
    (hf : M.func? s = some f) (hs : (M.table.summary s).mayPoison = false)
    (args : HVector toType (f.params.map (·.2))) (hargs : ¬ args.Any TyPoison.IsPoison)
    (fuel : Nat) (vs : List (DVal d)) :
    (f.run (m := SetM) M args fuel).run (.ok (.ok (.ret vs))) → DVals.Clean vs := by
  intro h
  simp only [Func.run] at h
  obtain ⟨⟨body, env⟩, hen, h⟩ := (run_liftExcept_bind (by intro _ h; cases h)).1 h
  obtain ⟨hops, rfl⟩ := Func.enter_ops hen
  rcases (run_bind _ _ _).1 h with ⟨x, hx, h⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · rcases x with ⟨vs', k⟩ | _ <;> cases (run_pure _ _).1 h
    have henv : Env.Clean ((f.params.map (·.1)).zip args.toDVals) := by
      simpa using (show Env.Clean ([] : Env d) from fun _ h => nomatch h).bind
        (f.params.map (·.1)) ((HVector.clean_toDVals args).2 hargs)
    exact Module.runOps_clean hv fuel s f _ body vs k hf hs henv hops hx
  · cases he
  · cases he

end Fir
