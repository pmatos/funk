import Fir.Execution.MemoryCallSteps
import Fir.Execution.MemoryTotal

/-!
# Progress and no stuck path, with memory

A run with memory of a function is never stuck, and has an outcome at every
budget, when every function of its module is valid and runs within the
module with memory, calls and recursion included, whatever its ops do to
the memories.

The proof is the proof for runs in the set monad (the section on progress
with calls), read from given memories (the section on how a run with memory
ends), and stands beside it (ADR-2026-11-11-0801). It is by induction on
the budget, for every function of the module at once, from any op of any
of its blocks on, and from any memories. Its invariant is the one of the
section on jumps: before an op, the environment holds every value in scope
at the op. Each step goes on from the memories that the step before it
ended with, and the claim holds from every memories, so it covers the rest
of the run from those. A call runs its callee from the memories with a new
frame entered, which the induction covers, and leaves the frame on each
path that returns, from which the caller goes on.

Showing that no path is stuck needs nothing of the ops' semantics: an op
that may end in many ways, from any memories, is never stuck in any of
them. Progress needs each op that runs by its own rule to have an outcome
from the memories it starts from, which a dialect lawful in its totality
gives at every naming.
-/

namespace Fir

open SetM Memory

/-! # Runs of ops with memory -/

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]
  [DialectValidation d] {ctx : ModuleContext d} {M : Module d}

/-- No path of a run with memory of a function of the module `M` is stuck,
from any op of any of its blocks on, with an environment that holds the
values in scope there, from any memories, when every function of `M` is
valid and runs within `M` with memory. -/
theorem Module.calls_memNoStuck (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.MemInModule unit M) (n : Nat) :
    ∀ f ∈ M.funcs, ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → ∀ S : Memories Mem unit,
        NoStuck (fromState (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env
          (b.body.drop i)) S) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hf b hb i env hi hold S
    cases n with
    | zero => simp only [Func.runOps, fromState_pure]; exact NoStuck.pure'
    | succ n =>
    have hvf := hv f hf
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hvf hb hi hold
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg]), hargs, liftExcept_ok_bind]
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine NoStuck.fromState_bind (NoStuck.fromState_lift _ _) fun x S' hx => ?_
      have hex := fromState_lift_ok hx
      cases x with
      | ret =>
        rw [ite_eq_left ((hm f hf).returns b hb _ ho hT args _ _ hex), fromState_pure]
        exact NoStuck.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := (hm f hf).jumps b hb _ ho hT args _ k _ hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hvf hb hi hold hT hres hk
        dsimp only
        rw [hj, liftExcept_ok_bind]
        have hns := ih n (Nat.lt_succ_self n) f hf tgt htm 0 env'
          (List.length_pos_iff.2 (hvf.blocksNonEmpty tgt htm)) hold' S'
        rwa [List.drop_zero] at hns
    · rename_i hT
      have hTf : isTerminator b.body[i].op = false := by simpa using hT
      split
      · refine NoStuck.fromState_bind (NoStuck.fromState_lift _ _) fun rs S' _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        rw [Env.bind_ok _ _ hlen, liftExcept_ok_bind]
        exact ih n (Nat.lt_succ_self n) f hf b hb (i + 1) _ (hnext hTf)
          (Func.scoped_next hvf hb hi hold rs hrty) S'
      · rename_i s heq
        obtain ⟨g, hg, hgm, hgp, hgr⟩ :=
          Module.func?_of_symbols ((hm f hf).calls b hb _ ho hTf s heq)
        have hvg := hv g hgm
        obtain ⟨e, he, hep⟩ := hvg.entry
        have hem : e ∈ g.blocks := List.mem_of_mem_head? he
        have hty : args.toDVals.map (·.1) = g.params.map (·.2) :=
          (HVector.toDVals_types args).trans hgp.symm
        simp only [hg, Func.enter_ok he hep hty, liftExcept_ok_bind]
        have hns := fun S => ih n (Nat.lt_succ_self n) g hgm e hem 0 _
          (List.length_pos_iff.2 (hvg.blocksNonEmpty e hem)) (Env.scoped_entry hvg he hep hty) S
        simp only [List.drop_zero] at hns
        refine NoStuck.fromState_bind ?_ fun r S' hr => ?_
        · rw [fromState_inFrame]
          exact NoStuck.map _ (hns _)
        match r, hr with
        | .fuelExhausted, _ => rw [fromState_pure]; exact NoStuck.pure'
        | .ret (vs, k), hr =>
          have hvs : vs.map (·.1) = returnTypes b.body[i].op :=
            ((Func.runOps_memReturns M n g _ _).inFrame S vs k S' hr).trans hgr
          have hlen : (b.body[i].results.map (·.1)).length = vs.length := by
            have h1 := congrArg List.length hvs
            have h2 := congrArg List.length hrty
            simp only [List.length_map] at h1 h2 ⊢
            omega
          simp only [hvs, ite_true, Env.bind_ok _ _ hlen, liftExcept_ok_bind]
          exact ih (min k n) (Nat.lt_succ_of_le (Nat.min_le_right _ _)) f hf b hb (i + 1) _
            (hnext hTf) (Func.scoped_results hvf hb hi hold (hvs.trans hrty.symm)) S'

/-- A run with memory of a function of the module `M` has a path, from any
op of any of its blocks on, with an environment that holds the values in
scope there, from any memories, when every function of `M` is valid and
runs within `M` with memory, and every op of `M` that runs by its own rule
has an outcome from any memories. -/
theorem Module.calls_memHasPath (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.MemInModule unit M)
    (ht : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body,
      isTerminator o.op = true ∨ callee? o.op = none →
        OpHasOutcome (σ := Memories Mem unit) o.op) (n : Nat) :
    ∀ f ∈ M.funcs, ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → ∀ S : Memories Mem unit,
        HasPath (fromState (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env
          (b.body.drop i)) S) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hf b hb i env hi hold S
    cases n with
    | zero => simp only [Func.runOps, fromState_pure]; exact HasPath.pure'
    | succ n =>
    have hvf := hv f hf
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hvf hb hi hold
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg]), hargs, liftExcept_ok_bind]
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine HasPath.fromState_bind
        (HasPath.fromState_lift ((ht f hf b hb _ ho (.inl hT) args).2 hT S)) fun x S' hx => ?_
      have hex := fromState_lift_ok hx
      cases x with
      | ret =>
        rw [ite_eq_left ((hm f hf).returns b hb _ ho hT args _ _ hex), fromState_pure]
        exact HasPath.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := (hm f hf).jumps b hb _ ho hT args _ k _ hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hvf hb hi hold hT hres hk
        dsimp only
        rw [hj, liftExcept_ok_bind]
        have hhp := ih n (Nat.lt_succ_self n) f hf tgt htm 0 env'
          (List.length_pos_iff.2 (hvf.blocksNonEmpty tgt htm)) hold' S'
        rwa [List.drop_zero] at hhp
    · rename_i hT
      have hTf : isTerminator b.body[i].op = false := by simpa using hT
      split
      · rename_i hc
        refine HasPath.fromState_bind
          (HasPath.fromState_lift ((ht f hf b hb _ ho (.inr hc) args).1 hTf S)) fun rs S' _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        rw [Env.bind_ok _ _ hlen, liftExcept_ok_bind]
        exact ih n (Nat.lt_succ_self n) f hf b hb (i + 1) _ (hnext hTf)
          (Func.scoped_next hvf hb hi hold rs hrty) S'
      · rename_i s heq
        obtain ⟨g, hg, hgm, hgp, hgr⟩ :=
          Module.func?_of_symbols ((hm f hf).calls b hb _ ho hTf s heq)
        have hvg := hv g hgm
        obtain ⟨e, he, hep⟩ := hvg.entry
        have hem : e ∈ g.blocks := List.mem_of_mem_head? he
        have hty : args.toDVals.map (·.1) = g.params.map (·.2) :=
          (HVector.toDVals_types args).trans hgp.symm
        simp only [hg, Func.enter_ok he hep hty, liftExcept_ok_bind]
        have hhp := fun S => ih n (Nat.lt_succ_self n) g hgm e hem 0 _
          (List.length_pos_iff.2 (hvg.blocksNonEmpty e hem)) (Env.scoped_entry hvg he hep hty) S
        simp only [List.drop_zero] at hhp
        refine HasPath.fromState_bind ?_ fun r S' hr => ?_
        · rw [fromState_inFrame]
          exact HasPath.map _ (hhp _)
        match r, hr with
        | .fuelExhausted, _ => rw [fromState_pure]; exact HasPath.pure'
        | .ret (vs, k), hr =>
          have hvs : vs.map (·.1) = returnTypes b.body[i].op :=
            ((Func.runOps_memReturns M n g _ _).inFrame S vs k S' hr).trans hgr
          have hlen : (b.body[i].results.map (·.1)).length = vs.length := by
            have h1 := congrArg List.length hvs
            have h2 := congrArg List.length hrty
            simp only [List.length_map] at h1 h2 ⊢
            omega
          simp only [hvs, ite_true, Env.bind_ok _ _ hlen, liftExcept_ok_bind]
          exact ih (min k n) (Nat.lt_succ_of_le (Nat.min_le_right _ _)) f hf b hb (i + 1) _
            (hnext hTf) (Func.scoped_results hvf hb hi hold (hvs.trans hrty.symm)) S'

end

/-! # The run of a function with memory -/

section

variable {α β : Type} {X : ExceptT Stuck SetM (Result (α × Nat))} (g : α → β)

/-- What a function does with its ops' run has no stuck path when the run
has none. -/
theorem NoStuck.finish (h : NoStuck X) : NoStuck (Result.finish g X) :=
  NoStuck.bind h fun r _ => by cases r <;> exact NoStuck.pure'

/-- What a function does with its ops' run has a path when the run has
one. -/
theorem HasPath.finish (h : HasPath X) : HasPath (Result.finish g X) :=
  HasPath.bind h fun r _ => by cases r <;> exact HasPath.pure'

end

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] [DialectValidation d] {N : Type} [DecidableEq N]
  (unit : N → Nat) (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d} {M : Module d}

/-- No path of a run with memory of a function of the module `M` is stuck,
at any budget, on any argument vector, calls and recursion included,
wherever a run names the dialect's memories, when every function of `M` is
valid and runs within `M` with memory at that naming. -/
theorem Func.memNeverStuck (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModuleAt unit ρ M) {f : Func d} (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns unit ρ M args) := by
  letI := DialectMemDenote.denoteAt (d := d) unit ρ
  intro n ⟨st, h⟩
  have hvf := hv f hf
  obtain ⟨e, he, hep⟩ := hvf.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hns := Module.calls_memNoStuck hv hm n f hf e hmem 0 _
    (List.length_pos_iff.2 (hvf.blocksNonEmpty e hmem)) (Env.scoped_params hvf he hep args)
    Memories.empty.enter
  rw [List.drop_zero] at hns
  rw [Func.memRuns_enter unit ρ M f args n (Func.enter_entry he hep args)] at h
  exact NoStuck.finish _ (NoStuck.map Result.withState hns) st h

/-- A run with memory of a function of the module `M` has an outcome at
every budget, on any argument vector, calls and recursion included,
wherever a run names the dialect's memories, when the dialect is lawful in
its totality and every function of `M` is valid and runs within `M` with
memory at that naming. -/
theorem Func.memProgress [LawfulDialectTotal d] (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModuleAt unit ρ M) {f : Func d} (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns unit ρ M args) := by
  letI := DialectMemDenote.denoteAt (d := d) unit ρ
  intro n
  have hvf := hv f hf
  obtain ⟨e, he, hep⟩ := hvf.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hpos := List.length_pos_iff.2 (hvf.blocksNonEmpty e hmem)
  have hold := Env.scoped_params hvf he hep args
  have hhp := Module.calls_memHasPath hv hm
    (fun g hg _ hb o ho hc => LawfulDialectTotal.total o.op ((hv g hg).typesValid hb ho) hc unit ρ)
    n f hf e hmem 0 _ hpos hold Memories.empty.enter
  have hns := Module.calls_memNoStuck hv hm n f hf e hmem 0 _ hpos hold Memories.empty.enter
  rw [List.drop_zero] at hhp hns
  rw [Func.memRuns_enter unit ρ M f args n (Func.enter_entry he hep args)]
  obtain ⟨ev, hev⟩ := HasPath.finish Prod.fst (HasPath.map Result.withState hhp)
  match ev, hev with
  | .ok (.ok (.ret vs)), hev => exact ⟨.ret vs, hev⟩
  | .ok (.ok .fuelExhausted), hev => exact ⟨.fuelExhausted, hev⟩
  | .ub r, hev => exact ⟨.ub r, hev⟩
  | .ok (.error st), hev => exact absurd hev (NoStuck.finish _ (NoStuck.map Result.withState hns) st)

end

end Fir
