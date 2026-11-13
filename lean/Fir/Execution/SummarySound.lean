import Fir.Execution.SummaryFixpoint
import Fir.Execution.SummaryClean
import Fir.Execution.MemoryCalls
import Fir.Execution.MemoryCallSteps
import Fir.Execution.EffectLaws

/-!
# Function summaries are sound

A pass may rely on a function's summary as it relies on an op's effects,
because the summary is proved sound: an effect that it leaves out, a run
of the function does not have (ADR-2026-11-09-1541). In a dialect lawful in
its effects, for a function of a module whose functions are all valid, its
runs with memory (the section on runs with memory) meet both, wherever a run
names the dialect's memories, whatever its ops do to the memories:

* _No may-UB_: when its summary leaves out may-UB, no run of the function
  ends in UB, at any budget of fuel.
* _No may produce poison_: when its summary leaves out may produce poison,
  a run of the function on arguments with no poison returns no poison
  (ADR-2026-11-09-1541).

Both hold of its runs from given memories too, which is how a call runs
its callee: from the memories its caller reached.

The proofs follow a run with memory op by op, by induction on its fuel,
from any memories, as the proofs of progress with memory do. Each op that
runs by its own rule leaves out each effect that its function's summary
leaves out, and so does every function it calls; each callee runs with less
fuel, from the memories its caller reached with a new frame entered, so the
induction covers its run, recursion included.

* An op that runs by its own rule, a terminator or an op with no callee,
  is covered by the obligations of a dialect lawful in its effects, which
  speak of its semantics with memory, from any memories: it never ends in
  UB, and gives no poison on operands with no poison. No semantics in the
  set monad is asked for, so an op that touches memory is covered too.
* A call runs its callee, whose summary is below its caller's, so it leaves
  out the effects that its caller's leaves out.
* For poison, the run keeps an environment with no poison (the section on
  values with no poison): the arguments
  have none, the operands that it finds there have none, so neither do the
  results that an op gives, the values that a jump passes, the arguments
  of a callee, or the values that a callee returns.
-/

namespace Fir

open SetM Memory

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

/-! # Runs of ops with memory, from any memories -/

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] [TyDenote d.Ty] [DecidableEq d.Ty]
  [TyPoison d.Ty] [DialectEffects d] [DialectValidation d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] {ctx : ModuleContext d} {M : Module d}

omit [TyPoison d.Ty] [DialectEffects d] [DialectValidation d] in
/-- A run in a call's frame hits UB only where its ops hit UB, from the
memories with a frame entered. -/
theorem Func.memCall_ub {M : Module d} {n : Nat} {g : Func d} {genv : Env d}
    {body : List (Operation d)} {S : Memories Mem unit} {r : String}
    (h : (Func.memCall M n g genv body S).run (.ub r)) :
    (Func.memOps M n g genv body S.enter).run (.ub r) := by
  rw [Func.memCall_eq] at h
  rcases (SetM.run_map _ _ _).1 h with ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, hu, he⟩
  · cases he
  · cases he
  · cases he
    exact hu

omit [TyPoison d.Ty] [DialectEffects d] [DialectValidation d] in
/-- A run in a call's frame returns what its ops return, from the memories
with a frame entered, with the frame left. -/
theorem Func.memCall_ret {M : Module d} {n : Nat} {g : Func d} {genv : Env d}
    {body : List (Operation d)} {S : Memories Mem unit} {vs : List (DVal d)}
    {S' : Memories Mem unit} {k : Nat}
    (h : (Func.memCall M n g genv body S).run (.ok (.ok (.ret ((vs, S'), k))))) :
    ∃ T, (Func.memOps M n g genv body S.enter).run (.ok (.ok (.ret ((vs, T), k)))) := by
  rw [Func.memCall_eq] at h
  rcases (SetM.run_map _ _ _).1 h with ⟨a, ha, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · match a, ha, he with
    | .ret ((_, T), _), ha, he =>
      cases he
      exact ⟨T, ha⟩
    | .fuelExhausted, _, he => cases he
  · cases he
  · cases he

omit [TyPoison d.Ty] in
/-- No run with memory of ops of a function of `M` ends in UB when the
function's summary leaves out may-UB, from any of its ops on, from any
memories, at any budget, when each valid op that runs by its own rule and
leaves out may-UB never ends in UB. -/
theorem Module.memOps_notUB (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hub : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
      (effects op).mayUB = false → ∀ args : HVector toType (sig op),
        (isTerminator op = false →
          NoUB (DialectDenote.denote (m := StateT (Memories Mem unit) SetM) op args)) ∧
        (isTerminator op = true →
          NoUB (DialectDenote.exit (m := StateT (Memories Mem unit) SetM) op args)))
    (n : Nat) :
    ∀ (s : Name) (f : Func d) (env : Env d) (os : List (Operation d)) (S : Memories Mem unit)
      (r : String), M.func? s = some f → (M.table.summary s).mayUB = false →
      (∀ o ∈ os, ∃ b ∈ f.blocks, o ∈ b.body) → ¬ (Func.memOps M n f env os S).run (.ub r) := by
  have hne : ∀ r : String, Ev.NotStuck (.ub r :
      Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))) :=
    fun _ _ h => nomatch h
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s f env os S r hf hs hos h
  have hfm : f ∈ M.funcs := List.mem_of_find?_eq_some hf
  cases n with
  | zero => cases Func.run_memOps_zero.1 h
  | succ n =>
  cases os with
  | nil => exact Func.run_memOps_nil (hne r) h
  | cons o os =>
  obtain ⟨b, hb, ho⟩ := hos o List.mem_cons_self
  have htv := (hv f hfm).typesValid hb ho
  have hown : (effects o.op).mayUB = false := by
    cases he : (effects o.op).mayUB
    · rfl
    · exact absurd ((M.table.effects_le_summary hf (Func.mem_allOps hb ho)).mayUB he) (by simp [hs])
  have htail : ∀ o' ∈ os, ∃ b ∈ f.blocks, o' ∈ b.body :=
    fun o' h' => hos o' (List.mem_cons_of_mem _ h')
  cases (Func.memStepPath_iff (hne r)).1 h with
  | exitUB _ _ hT _ hx => exact (hub o.op htv (.inl hT) hown _).2 hT S r hx
  | goto _ _ _ _ _ hj hrun =>
    obtain ⟨_, _, _, hblk, -⟩ := Func.jump_eq_ok hj
    exact ih n (Nat.lt_succ_self n) s f _ _ _ r hf hs
      (fun o' h' => ⟨_, (Func.block?_some hblk).1, h'⟩) hrun
  | denoteUB _ _ hT hc hx => exact (hub o.op htv (.inr hc) hown _).1 hT S r hx
  | denote _ _ _ _ _ _ hrun => exact ih n (Nat.lt_succ_self n) s f _ os _ r hf hs htail hrun
  | @callUB _ c g _ _ _ _ _ hT hc hg hen hx =>
    have hg' : M.table.func? c = some g := hg
    have hcs : (M.table.summary c).mayUB = false := by
      cases he : (M.table.summary c).mayUB
      · rfl
      · exact absurd ((M.table.summary_closed.calls s f hf o (Func.mem_allOps hb ho) c
          (Operation.call?_of hT hc) (by simp [hg'])).mayUB he) (by simp [hs])
    exact ih n (Nat.lt_succ_self n) c g _ _ _ _ hg hcs (Func.enter_ops hen).1 (Func.memCall_ub hx)
  | callRet _ _ _ _ _ _ _ _ _ hrun =>
    exact ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) s f _ os _ r hf hs htail hrun

/-- A run with memory of ops of a function of `M` returns no poison when the
function's summary leaves out may produce poison and its environment has
none, from any of its ops on, from any memories, at any budget, when each
valid op with no callee that leaves out may produce poison gives no poison
on operands with none. -/
theorem Module.memOps_clean (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hnp : ∀ op : d.Op, TypesValid op → isTerminator op = false → callee? op = none →
      (effects op).mayPoison = false → ∀ args : HVector toType (sig op),
        ¬ args.Any TyPoison.IsPoison → ∀ S rs S',
          DialectDenote.denote (m := StateT (Memories Mem unit) SetM) op args S (.ok (rs, S')) →
            ¬ rs.Any TyPoison.IsPoison)
    (n : Nat) :
    ∀ (s : Name) (f : Func d) (env : Env d) (os : List (Operation d)) (S : Memories Mem unit)
      (vs : List (DVal d)) (S' : Memories Mem unit) (k : Nat), M.func? s = some f →
      (M.table.summary s).mayPoison = false → env.Clean →
      (∀ o ∈ os, ∃ b ∈ f.blocks, o ∈ b.body) →
      (Func.memOps M n f env os S).run (.ok (.ok (.ret ((vs, S'), k)))) → DVals.Clean vs := by
  have hne : ∀ (vs : List (DVal d)) (S' : Memories Mem unit) (k : Nat),
      Ev.NotStuck (.ok (.ok (.ret ((vs, S'), k))) :
        Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))) :=
    fun _ _ _ _ h => nomatch h
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s f env os S vs S' k hf hs henv hos h
  have hfm : f ∈ M.funcs := List.mem_of_find?_eq_some hf
  cases n with
  | zero => cases Func.run_memOps_zero.1 h
  | succ n =>
  cases os with
  | nil => exact absurd h (Func.run_memOps_nil (hne vs S' k))
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
  cases (Func.memStepPath_iff (hne vs S' k)).1 h with
  | ret _ hargs _ _ _ _ => exact (HVector.clean_toDVals _).2 (henv.operands hargs)
  | goto _ _ _ _ _ hj hrun =>
    obtain ⟨_, vs', _, hblk, hvs, -, -, rfl⟩ := Func.jump_eq_ok hj
    exact ih n (Nat.lt_succ_self n) s f _ _ _ vs S' k hf hs (henv.bind _ (henv.mapM_value hvs))
      (fun o' h' => ⟨_, (Func.block?_some hblk).1, h'⟩) hrun
  | @denote args rs _ _ _ hargs hT hc hx _ hrun =>
    have hrs := hnp o.op htv hT hc hown args (henv.operands hargs) _ rs _ hx
    exact ih n (Nat.lt_succ_self n) s f _ os _ vs S' k hf hs
      (henv.bind _ ((HVector.clean_toDVals rs).2 hrs)) htail hrun
  | @callRet args c g _ _ vs' _ k' _ _ hargs hT hc hg hen hcallee _ _ hrun =>
    have hg' : M.table.func? c = some g := hg
    have hcs : (M.table.summary c).mayPoison = false := by
      cases he : (M.table.summary c).mayPoison
      · rfl
      · exact absurd ((M.table.summary_closed.calls s f hf o (Func.mem_allOps hb ho) c
          (Operation.call?_of hT hc) (by simp [hg'])).mayPoison he) (by simp [hs])
    obtain ⟨hops, rfl⟩ := Func.enter_ops hen
    obtain ⟨T, hT'⟩ := Func.memCall_ret hcallee
    have hvs' : DVals.Clean vs' := ih n (Nat.lt_succ_self n) c g _ _ _ _ T _ hg hcs
      (Env.Clean.params _ args (henv.operands hargs)) hops hT'
    exact ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) s f _ os _ vs S' k hf hs
      (henv.bind _ hvs') htail hrun

end

/-! # Function summaries with memory -/

variable [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty] [DialectEffects d]
  [DialectValidation d] [DialectMemDenote d] [LawfulDialectEffects d] {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d} {M : Module d}

/-- No run with memory of a function of `M` ends in UB when its summary
leaves out may-UB, at any budget of fuel, wherever a run names the dialect's
memories, when every function of `M` is valid and the dialect is lawful in
its effects. -/
theorem Module.summary_neverUB (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d}
    (hf : M.func? s = some f) (hs : (M.table.summary s).mayUB = false)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (r : String) :
    ¬ f.memRuns lay ρ M args fuel (.ub r) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro h
  obtain ⟨e, he, hep⟩ := (hv f (List.mem_of_find?_eq_some hf)).entry
  have hen := Func.enter_entry he hep args
  rw [Func.memRuns_enter lay ρ M f args fuel hen] at h
  unfold Result.finish at h
  rcases (run_bind _ _ _).1 h with ⟨x, _, h⟩ | ⟨_, _, he⟩ | ⟨_, hr, he⟩
  · rcases x with ⟨_, _⟩ | _ <;> cases (run_pure _ _).1 h
  · cases he
  · cases he
    exact Module.memOps_notUB hv
      (fun op hv' hc hown => LawfulDialectEffects.neverUB op hv' hc hown lay ρ)
      fuel s f _ _ _ _ hf hs (Func.enter_ops hen).1 hr

/-- A run with memory of a function of `M` on arguments with no poison
returns no poison when its summary leaves out may produce poison, at any
budget of fuel, wherever a run names the dialect's memories, when every
function of `M` is valid and the dialect is lawful in its effects. -/
theorem Module.summary_noPoison (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d}
    (hf : M.func? s = some f) (hs : (M.table.summary s).mayPoison = false)
    (args : HVector toType (f.params.map (·.2))) (hargs : ¬ args.Any TyPoison.IsPoison)
    (fuel : Nat) (vs : List (DVal d)) :
    f.memRuns lay ρ M args fuel (.ok (.ok (.ret vs))) → DVals.Clean vs := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro h
  obtain ⟨e, he, hep⟩ := (hv f (List.mem_of_find?_eq_some hf)).entry
  have hen := Func.enter_entry he hep args
  rw [Func.memRuns_enter lay ρ M f args fuel hen] at h
  unfold Result.finish at h
  obtain ⟨hops, -⟩ := Func.enter_ops hen
  have henv := Env.Clean.params (f.params.map (·.1)) args hargs
  rcases (run_bind _ _ _).1 h with ⟨x, hx, h⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · rcases x with ⟨⟨vs', S'⟩, k⟩ | _ <;> cases (run_pure _ _).1 h
    exact Module.memOps_clean hv
      (fun op hv' hT hc hown => LawfulDialectEffects.makesNoPoison op hv' (.inr hc) hown hT lay ρ)
      fuel s f _ e.body _ vs' S' k hf hs henv hops hx
  · cases he
  · cases he

/-- No run with memory of a function of `M` from given memories ends in UB
when its summary leaves out may-UB, at any budget of fuel, wherever a run
names the dialect's memories: a call runs its callee so, from its caller's
memories. -/
theorem Module.summary_neverUB_from (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func d}
    (hf : M.func? s = some f) (hs : (M.table.summary s).mayUB = false)
    (args : HVector toType (f.params.map (·.2))) (S : Memories N (unitsOf lay)) (fuel : Nat)
    (r : String) :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    ¬ f.memRunsFrom M (args, S) fuel (.ub r) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro h
  obtain ⟨⟨body, env⟩, hen, e, he, hx⟩ :=
    (Func.memRunsFrom_run (x := .ub r) (fun _ h => nomatch h)).1 h
  have hub : e = .ub r := by
    match e, hx with
    | .ub _, hx => cases hx; rfl
    | .ok (.ok (.ret _)), hx | .ok (.ok .fuelExhausted), hx | .ok (.error _), hx => cases hx
  subst hub
  exact Module.memOps_notUB hv
    (fun op hv' hc hown => LawfulDialectEffects.neverUB op hv' hc hown lay ρ)
    fuel s f _ _ _ _ hf hs (Func.enter_ops hen).1 (Func.memCall_ub he)

/-- A run with memory of a function of `M` from given memories, on arguments
with no poison, returns no poison when its summary leaves out may produce
poison, at any budget of fuel, wherever a run names the dialect's memories:
a call runs its callee so, from its caller's memories. -/
theorem Module.summary_noPoison_from (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name}
    {f : Func d} (hf : M.func? s = some f) (hs : (M.table.summary s).mayPoison = false)
    (args : HVector toType (f.params.map (·.2))) (hargs : ¬ args.Any TyPoison.IsPoison)
    (S : Memories N (unitsOf lay)) (fuel : Nat) (vs : List (DVal d))
    (S' : Memories N (unitsOf lay)) :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    f.memRunsFrom M (args, S) fuel (.ok (.ok (.ret (vs, S')))) → DVals.Clean vs := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro h
  obtain ⟨⟨body, env⟩, hen, e, he, hx⟩ :=
    (Func.memRunsFrom_run (x := .ok (.ok (.ret (vs, S')))) (fun _ h => nomatch h)).1 h
  have hret : ∃ k, e = .ok (.ok (.ret ((vs, S'), k))) := by
    match e, hx with
    | .ok (.ok (.ret (_, k))), hx => cases hx; exact ⟨k, rfl⟩
    | .ub _, hx | .ok (.ok .fuelExhausted), hx | .ok (.error _), hx => cases hx
  obtain ⟨k, rfl⟩ := hret
  obtain ⟨hops, rfl⟩ := Func.enter_ops hen
  obtain ⟨T, hT⟩ := Func.memCall_ret he
  exact Module.memOps_clean hv
    (fun op hv' hT hc hown => LawfulDialectEffects.makesNoPoison op hv' (.inr hc) hown hT lay ρ)
    fuel s f _ _ _ _ T _ hf hs (Env.Clean.params _ args hargs) hops hT

end Fir
