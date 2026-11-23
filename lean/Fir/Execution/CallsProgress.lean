import Fir.Execution.Calls

/-!
# A path at every budget, with calls

A valid function's run has an outcome at every budget, when every function
of its module is valid and runs within the module, and every op that runs
by its own rule, a terminator or an op with no callee, is total, and so is
the rule of every op whose callee is picked (#235). The proof follows the
one for no stuck path (`Fir.Execution.Calls`), by induction on the budget,
and finds a way on at each step: an op's outcome, which totality gives, or
its callee's run, which the induction covers.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

variable [DialectValidation d] {ctx : ModuleContext d} {M : Module d}

/-- A run of a function of the module `M` has a path, from any op of any of
its blocks on, with an environment that holds the values in scope there,
when every function of `M` is valid and runs within `M`, every op of `M`
that runs by its own rule, a terminator or an op with no callee, is total,
and so is the rule of every op of `M` whose callee is picked. -/
theorem Module.calls_hasPath (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M)
    (ht : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body,
      isTerminator o.op = true ∨ callee? o.op = none → OpTotal o.op)
    (hpt : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body, callee? o.op = some .picked →
      PickTotal o.op) (n : Nat) :
    ∀ f ∈ M.funcs, ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → HasPath (Func.runOps (m := SetM) M n f env (b.body.drop i)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hf b hb i env hi hold
    cases n with
    | zero => simp only [Func.runOps]; exact HasPath.pure'
    | succ n =>
    have hvf := hv f hf
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hvf hb hi hold
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg])]
    refine HasPath.bind_ok (a := args) ?_ ?_
    · rw [hargs]; rfl
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine HasPath.bind_lift ((ht f hf b hb _ ho (.inl hT) args).2 hT) fun x hex => ?_
      cases x with
      | ret => rw [ite_eq_left ((hm f hf).returns b hb _ ho hT args hex)]; exact HasPath.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := (hm f hf).jumps b hb _ ho hT args k hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hvf hb hi hold hT hres hk
        have hhp := ih n (by omega) f hf tgt htm 0 env'
          (List.length_pos_iff.2 (hvf.blocksNonEmpty tgt htm)) hold'
        rw [List.drop_zero] at hhp
        refine HasPath.bind_ok (a := (tgt, env')) ?_ hhp
        rw [hj]
        rfl
    · rename_i hT
      have hTf : isTerminator b.body[i].op = false := by simpa using hT
      split
      · rename_i hc
        refine HasPath.bind_lift ((ht f hf b hb _ ho (.inr hc) args).1 hTf) fun rs _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        refine HasPath.bind_ok ?_ (ih n (by omega) f hf b hb (i + 1) _ (hnext hTf)
          (Func.scoped_next hvf hb hi hold rs hrty))
        rw [Env.bind_ok _ _ hlen]
        rfl
      · rename_i s heq
        obtain ⟨g, hg, hgm, hgp, hgr⟩ :=
          Module.func?_of_symbols ((hm f hf).calls b hb _ ho hTf s heq)
        have hvg := hv g hgm
        obtain ⟨e, he, hep⟩ := hvg.entry
        have hem : e ∈ g.blocks := List.mem_of_mem_head? he
        have hty : args.toDVals.map (·.1) = g.params.map (·.2) :=
          (HVector.toDVals_types args).trans hgp.symm
        simp only [hg, Func.enter_ok he hep hty]
        refine HasPath.bind_ok (a := (e.body, _)) rfl ?_
        have hhp := ih n (by omega) g hgm e hem 0 _
          (List.length_pos_iff.2 (hvg.blocksNonEmpty e hem)) (Env.scoped_entry hvg he hep hty)
        rw [List.drop_zero] at hhp
        refine HasPath.bind hhp fun r hr => ?_
        match r, hr with
        | .fuelExhausted, _ => exact HasPath.pure'
        | .ret (vs, k), hr =>
          have hvs : vs.map (·.1) = returnTypes b.body[i].op :=
            (Func.runOps_returns M n g _ _ vs k hr).trans hgr
          have hlen : (b.body[i].results.map (·.1)).length = vs.length := by
            have h1 := congrArg List.length hvs
            have h2 := congrArg List.length hrty
            simp only [List.length_map] at h1 h2 ⊢
            omega
          simp only [hvs, ite_true, Env.bind_ok _ _ hlen]
          exact HasPath.bind_ok rfl (ih (min k n) (Nat.lt_succ_of_le (Nat.min_le_right _ _)) f hf
            b hb (i + 1) _ (hnext hTf) (Func.scoped_results hvf hb hi hold (hvs.trans hrty.symm)))
      · rename_i heq
        refine HasPath.bind_lift (hpt f hf b hb _ ho heq _ args) fun s hs => ?_
        cases n with
        | zero => exact HasPath.pure'
        | succ n =>
        dsimp only
        have hok := (hm f hf).picks b hb _ ho hTf heq args s hs
        unfold Module.callable at hok
        split at hok
        · rename_i g hg
          simp only [Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨hgp, hgr⟩ := hok
          have hgm : g ∈ M.funcs := List.mem_of_find?_eq_some hg
          have hvg := hv g hgm
          obtain ⟨e, he, hep⟩ := hvg.entry
          have hem : e ∈ g.blocks := List.mem_of_mem_head? he
          have hty : args.tail.toDVals.map (·.1) = g.params.map (·.2) := by
            rw [HVector.toDVals_types]; exact hgp.symm
          simp only [Func.enter_ok he hep hty]
          refine HasPath.bind_ok (a := (e.body, _)) rfl ?_
          have hhp := ih n (by omega) g hgm e hem 0 _
            (List.length_pos_iff.2 (hvg.blocksNonEmpty e hem)) (Env.scoped_entry hvg he hep hty)
          rw [List.drop_zero] at hhp
          refine HasPath.bind hhp fun r hr => ?_
          match r, hr with
          | .fuelExhausted, _ => exact HasPath.pure'
          | .ret (vs, k), hr =>
            have hvs : vs.map (·.1) = returnTypes b.body[i].op :=
              (Func.runOps_returns M n g _ _ vs k hr).trans hgr
            have hlen : (b.body[i].results.map (·.1)).length = vs.length := by
              have h1 := congrArg List.length hvs
              have h2 := congrArg List.length hrty
              simp only [List.length_map] at h1 h2 ⊢
              omega
            simp only [hvs, ite_true, Env.bind_ok _ _ hlen]
            exact HasPath.bind_ok rfl (ih (min k n) (by omega) f hf
              b hb (i + 1) _ (hnext hTf) (Func.scoped_results hvf hb hi hold (hvs.trans hrty.symm)))
        · simp only [hok, ↓reduceIte]
          exact HasPath.bind_lift ⟨_, rfl⟩ fun _ hvs => by cases hvs

/-- A run of a function of the module `M` has an outcome at every budget,
on any argument vector, calls and recursion included, when every function
of `M` is valid and runs within `M`, every op of `M` that runs by its own
rule, a terminator or an op with no callee, is total, and so is the rule
of every op of `M` whose callee is picked. -/
theorem Func.progress_of_inModule (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M)
    (ht : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body,
      isTerminator o.op = true ∨ callee? o.op = none → OpTotal o.op)
    (hpt : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body, callee? o.op = some .picked →
      PickTotal o.op) {f : Func d}
    (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    Progress (f.runs M args) := by
  intro n
  have hvf := hv f hf
  obtain ⟨e, he, hep⟩ := hvf.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hpos := List.length_pos_iff.2 (hvf.blocksNonEmpty e hmem)
  have hold := Env.scoped_params hvf he hep args
  obtain ⟨ev, hev⟩ := Module.calls_hasPath hv hm ht hpt n f hf e hmem 0 _ hpos hold
  have hns := Module.calls_noStuck hv hm n f hf e hmem 0 _ hpos hold
  rw [List.drop_zero] at hev hns
  have hrun := (Func.run_run M f args n ev.dropLeft).2
    (.inl ⟨_, Func.enter_entry he hep args, ev, hev, rfl⟩)
  match ev, hev, hrun with
  | .ok (.ok (.ret (vs, _))), _, hrun => exact ⟨.ret vs, hrun⟩
  | .ok (.ok .fuelExhausted), _, hrun => exact ⟨.fuelExhausted, hrun⟩
  | .ub r, _, hrun => exact ⟨.ub r, hrun⟩
  | .ok (.error st), hev, _ => exact absurd hev (hns st)

end Fir
