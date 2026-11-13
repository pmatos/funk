import Fir.Execution.MemoryProgress

/-!
# Progress and no stuck path with memory, without calls

A function none of whose ops calls a function runs only its own ops, so
its run with memory needs nothing of the other functions of its module:
when it is valid and runs within its module with memory, no path of its
run with memory is stuck, and, when its ops are total with memory, its run
has an outcome at every budget, whatever its module and whatever its ops do
to the memories. Its module need not be valid, nor even hold it.

The proof is the proof of the section on progress with memory, with no
call to follow: by induction on the budget, from any op of any of its
blocks on, from any memories. Each step goes on from the memories that the
step before it ended with, and the claim holds from every memories, so it
covers the rest of the run from those. It stands beside the theorems on
local functions of the section on jumps and loops, which speak of runs in
the set monad.
-/

namespace Fir

open SetM Memory

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]
  [DialectValidation d] {ctx : ModuleContext d} {M : Module d} {f : Func d}

/-- No path of a run with memory of a valid function none of whose ops
calls a function is stuck, from any op of any of its blocks on, with an
environment that holds the values in scope there, from any memories, when
it runs within its module with memory. -/
theorem Func.local_memNoStuck (hv : f.Valid ctx)
    (hn : ∀ b ∈ f.blocks, ∀ o ∈ b.body, callee? o.op = none) (hm : f.MemInModule unit M)
    (n : Nat) :
    ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → ∀ S : Memories Mem unit,
        NoStuck (fromState (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env
          (b.body.drop i)) S) := by
  induction n with
  | zero => intro _ _ _ _ _ _ _; simp only [Func.runOps, fromState_pure]; exact NoStuck.pure'
  | succ n ih =>
    intro b hb i env hi hold S
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hv hb hi hold
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
        rw [ite_eq_left (hm.returns b hb _ ho hT args _ _ hex), fromState_pure]
        exact NoStuck.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := hm.jumps b hb _ ho hT args _ k _ hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hv hb hi hold hT hres hk
        dsimp only
        rw [hj, liftExcept_ok_bind]
        have hns := ih tgt htm 0 env' (List.length_pos_iff.2 (hv.blocksNonEmpty tgt htm)) hold' S'
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
        exact ih b hb (i + 1) _ (hnext hTf) (Func.scoped_next hv hb hi hold rs hrty) S'
      · rename_i heq
        rw [hn b hb _ ho] at heq
        cases heq

/-- A run with memory of a valid function none of whose ops calls a
function has a path, from any op of any of its blocks on, with an
environment that holds the values in scope there, from any memories, when it
runs within its module with memory and each of its ops has an outcome from
any memories. -/
theorem Func.local_memHasPath (hv : f.Valid ctx)
    (hn : ∀ b ∈ f.blocks, ∀ o ∈ b.body, callee? o.op = none) (hm : f.MemInModule unit M)
    (ht : ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpHasOutcome (σ := Memories Mem unit) o.op) (n : Nat) :
    ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → ∀ S : Memories Mem unit,
        HasPath (fromState (Func.runOps (m := StateT (Memories Mem unit) SetM) M n f env
          (b.body.drop i)) S) := by
  induction n with
  | zero => intro _ _ _ _ _ _ _; simp only [Func.runOps, fromState_pure]; exact HasPath.pure'
  | succ n ih =>
    intro b hb i env hi hold S
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hv hb hi hold
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg]), hargs, liftExcept_ok_bind]
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine HasPath.fromState_bind
        (HasPath.fromState_lift ((ht b hb _ ho args).2 hT S)) fun x S' hx => ?_
      have hex := fromState_lift_ok hx
      cases x with
      | ret =>
        rw [ite_eq_left (hm.returns b hb _ ho hT args _ _ hex), fromState_pure]
        exact HasPath.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := hm.jumps b hb _ ho hT args _ k _ hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hv hb hi hold hT hres hk
        dsimp only
        rw [hj, liftExcept_ok_bind]
        have hhp := ih tgt htm 0 env' (List.length_pos_iff.2 (hv.blocksNonEmpty tgt htm)) hold' S'
        rwa [List.drop_zero] at hhp
    · rename_i hT
      have hTf : isTerminator b.body[i].op = false := by simpa using hT
      split
      · refine HasPath.fromState_bind
          (HasPath.fromState_lift ((ht b hb _ ho args).1 hTf S)) fun rs S' _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        rw [Env.bind_ok _ _ hlen, liftExcept_ok_bind]
        exact ih b hb (i + 1) _ (hnext hTf) (Func.scoped_next hv hb hi hold rs hrty) S'
      · rename_i heq
        rw [hn b hb _ ho] at heq
        cases heq

end

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] [DialectValidation d] {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d}
  {M : Module d} {f : Func d}

/-- No path of a run with memory of a valid function none of whose ops
calls a function is stuck, at any budget, on any argument vector, jumps and
loops included, wherever a run names the dialect's memories, when it runs
within its module with memory at that naming. -/
theorem Func.memNeverStuck_of_local (hv : f.Valid ctx)
    (hn : ∀ b ∈ f.blocks, ∀ o ∈ b.body, callee? o.op = none) (hm : f.InModuleAt lay ρ M)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ M args) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro n ⟨st, h⟩
  obtain ⟨e, he, hep⟩ := hv.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hns := Func.local_memNoStuck hv hn hm n e hmem 0 _
    (List.length_pos_iff.2 (hv.blocksNonEmpty e hmem)) (Env.scoped_params hv he hep args)
    Memories.empty.enter
  rw [List.drop_zero] at hns
  rw [Func.memRuns_enter lay ρ M f args n (Func.enter_entry he hep args)] at h
  exact NoStuck.finish _ (NoStuck.map Result.withState hns) st h

/-- A run with memory of a valid function none of whose ops calls a
function has an outcome at every budget, on any argument vector, jumps and
loops included, wherever a run names the dialect's memories, when the
dialect is lawful in its totality and the function runs within its module
with memory at that naming. -/
theorem Func.memProgress_of_local [LawfulDialectTotal d] (hv : f.Valid ctx)
    (hn : ∀ b ∈ f.blocks, ∀ o ∈ b.body, callee? o.op = none) (hm : f.InModuleAt lay ρ M)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ M args) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro n
  obtain ⟨e, he, hep⟩ := hv.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hhp := Func.local_memHasPath hv hn hm
    (fun _ hb o ho => LawfulDialectTotal.total o.op (hv.typesValid hb ho) (.inr (hn _ hb o ho))
      lay ρ)
    n e hmem 0 _ (List.length_pos_iff.2 (hv.blocksNonEmpty e hmem))
    (Env.scoped_params hv he hep args) Memories.empty.enter
  rw [List.drop_zero] at hhp
  obtain ⟨ev, hev⟩ := HasPath.finish Prod.fst (HasPath.map Result.withState hhp)
  replace hev : f.memRuns lay ρ M args n ev := by
    rw [Func.memRuns_enter lay ρ M f args n (Func.enter_entry he hep args)]
    exact hev
  match ev, hev with
  | .ok (.ok (.ret vs)), hev => exact ⟨.ret vs, hev⟩
  | .ok (.ok .fuelExhausted), hev => exact ⟨.fuelExhausted, hev⟩
  | .ub r, hev => exact ⟨.ub r, hev⟩
  | .ok (.error st), hev =>
    exact absurd ⟨st, hev⟩ (Func.memNeverStuck_of_local lay ρ hv hn hm args n)

end

end Fir
