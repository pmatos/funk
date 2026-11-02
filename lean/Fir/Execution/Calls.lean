import Fir.Execution.CallSteps

/-!
# Progress and no stuck path, with calls and recursion

A valid function's run is never stuck, and has an outcome at every budget,
when every function of its module is valid and runs within the module
(`Func.InModule`): its terminators keep to the rules of the section on
jumps and loops, and each op that calls a function names one of the
module, of the right type.

* An op that calls a function, as its dialect's `callee?` says, names a
  symbol that the module's symbol table gives the type of the call: the
  call's operand types as its parameter types, and the call's result
  types as its result types. A dialect's own validation rule for a call
  must ask this, as the core rule for `call` does.
* A terminator that jumps names a successor that it has and gives no
  results, and a terminator that returns returns values of the function's
  result types, as for a function that runs within itself
  (`Func.Local`), which runs within every module (`Func.Local.inModule`).

Calls, recursion and mutual recursion are included: a run may call any
function of the module, itself among them, as often as its fuel allows.

The proof is by strong induction on the budget, for every function of the
module at once, from any op of any of its blocks on. Its invariant is the
one of the section on jumps, `Env.Scoped`. A call is the one new step:

* the module's symbol table names the callee, so the run finds it
  (`Module.func?_of_symbols`), and it is a function of the module;
* the call's operands have the callee's parameter types, so the callee's
  run starts at its entry block, with its parameters bound to them
  (`Func.enter_ok`), and its environment holds every value in scope there
  (`Env.scoped_entry`);
* the callee runs with fewer steps than the caller had, so the induction
  covers its run, however deep the calls go: no path of it is stuck, and
  it has one;
* each value that the callee returns has the callee's result type, which
  the interpreter checks before it returns (`Func.runOps_returns`), so it
  has the call's result type, and the call's results bind
  (`Func.scoped_results`);
* the caller goes on with the steps that the callee leaves, fewer again
  than it had, so the induction covers the rest of its run.

`NeverStuck` needs nothing more of the ops' semantics. `Progress` needs
each op to be total (`OpTotal`), so that each step has a way to go on. A
callee's run that ends with UB or out of fuel ends its caller's run so,
and that is a way for it to end.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- The ops of `f` run within the module `M`: an op that calls a function
names a symbol of `M` whose type is the call's, its operand types and its
result types; a terminator that jumps names a successor that it has, and
gives no results; and a terminator that returns returns values of `f`'s
result types. -/
structure Func.InModule (M : Module d) (f : Func d) : Prop where
  calls : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = false → ∀ s,
    callee? o.op = some s → M.symbols s = some ⟨sig o.op, returnTypes o.op⟩
  jumps : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → ∀ args i,
    DialectDenote.exit (m := SetM) o.op args (.ok (.goto i)) →
      i < succCount o.op ∧ returnTypes o.op = []
  returns : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → ∀ args,
    DialectDenote.exit (m := SetM) o.op args (.ok .ret) → sig o.op = f.results

omit [DecidableEq d.Ty] in
/-- A function that runs within itself runs within every module: it calls
no function. -/
theorem Func.Local.inModule {f : Func d} (hl : f.Local) (M : Module d) : f.InModule M where
  calls b hb o ho _ s h := by rw [hl.noCall b hb o ho] at h; cases h
  jumps := hl.jumps
  returns := hl.returns

variable [DialectValidation d] {ctx : ModuleContext d} {M : Module d}

/-- No path of a run of a function of the module `M` is stuck, from any op
of any of its blocks on, with an environment that holds the values in
scope there, when every function of `M` is valid and runs within `M`. -/
theorem Module.calls_noStuck (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M) (n : Nat) :
    ∀ f ∈ M.funcs, ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → NoStuck (Func.runOps (m := SetM) M n f env (b.body.drop i)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hf b hb i env hi hold
    cases n with
    | zero => simp only [Func.runOps]; exact NoStuck.pure'
    | succ n =>
    have hvf := hv f hf
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hvf hb hi hold
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg])]
    refine NoStuck.bind ?_ fun args' _ => ?_
    · rw [hargs]; exact NoStuck.liftExcept_ok
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine NoStuck.bind NoStuck.lift fun x hx => ?_
      have hex := exit_of_lift hx
      cases x with
      | ret => rw [ite_eq_left ((hm f hf).returns b hb _ ho hT args' hex)]; exact NoStuck.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := (hm f hf).jumps b hb _ ho hT args' k hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hvf hb hi hold hT hres hk
        refine NoStuck.bind ?_ fun p hp => ?_
        · rw [hj]; exact NoStuck.liftExcept_ok
        rw [hj] at hp
        cases (run_liftExcept _ _).1 hp
        have hns := ih n (Nat.lt_succ_self n) f hf tgt htm 0 env'
          (List.length_pos_iff.2 (hvf.blocksNonEmpty tgt htm)) hold'
        rwa [List.drop_zero] at hns
    · rename_i hT
      have hTf : isTerminator b.body[i].op = false := by simpa using hT
      split
      · refine NoStuck.bind NoStuck.lift fun rs _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        refine NoStuck.bind ?_ fun env' henv' => ?_
        · rw [Env.bind_ok _ _ hlen]; exact NoStuck.liftExcept_ok
        rw [Env.bind_ok _ _ hlen] at henv'
        cases (run_liftExcept _ _).1 henv'
        exact ih n (Nat.lt_succ_self n) f hf b hb (i + 1) _ (hnext hTf)
          (Func.scoped_next hvf hb hi hold rs hrty)
      · rename_i s heq
        obtain ⟨g, hg, hgm, hgp, hgr⟩ :=
          Module.func?_of_symbols ((hm f hf).calls b hb _ ho hTf s heq)
        have hvg := hv g hgm
        obtain ⟨e, he, hep⟩ := hvg.entry
        have hem : e ∈ g.blocks := List.mem_of_mem_head? he
        have hty : args'.toDVals.map (·.1) = g.params.map (·.2) :=
          (HVector.toDVals_types args').trans hgp.symm
        simp only [hg, Func.enter_ok he hep hty]
        refine NoStuck.bind NoStuck.liftExcept_ok fun p hp => ?_
        cases (run_liftExcept _ _).1 hp
        have hns := ih n (Nat.lt_succ_self n) g hgm e hem 0 _
          (List.length_pos_iff.2 (hvg.blocksNonEmpty e hem)) (Env.scoped_entry hvg he hep hty)
        rw [List.drop_zero] at hns
        refine NoStuck.bind hns fun r hr => ?_
        match r, hr with
        | .fuelExhausted, _ => exact NoStuck.pure'
        | .ret (vs, k), hr =>
          have hvs : vs.map (·.1) = returnTypes b.body[i].op :=
            (Func.runOps_returns M n g _ _ vs k hr).trans hgr
          have hlen : (b.body[i].results.map (·.1)).length = vs.length := by
            have h1 := congrArg List.length hvs
            have h2 := congrArg List.length hrty
            simp only [List.length_map] at h1 h2 ⊢
            omega
          simp only [hvs, ite_true, Env.bind_ok _ _ hlen]
          refine NoStuck.bind NoStuck.liftExcept_ok fun env' henv' => ?_
          cases (run_liftExcept _ _).1 henv'
          exact ih (min k n) (Nat.lt_succ_of_le (Nat.min_le_right _ _)) f hf b hb (i + 1) _
            (hnext hTf) (Func.scoped_results hvf hb hi hold (hvs.trans hrty.symm))

/-- A run of a function of the module `M` has a path, from any op of any of
its blocks on, with an environment that holds the values in scope there,
when every function of `M` is valid and runs within `M`, and every op of
`M` is total. -/
theorem Module.calls_hasPath (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M)
    (ht : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body, OpTotal o.op) (n : Nat) :
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
    have htot := ht f hf b hb _ ho args
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg])]
    refine HasPath.bind_ok (a := args) ?_ ?_
    · rw [hargs]; rfl
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine HasPath.bind_lift (htot.2 hT) fun x hex => ?_
      cases x with
      | ret => rw [ite_eq_left ((hm f hf).returns b hb _ ho hT args hex)]; exact HasPath.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := (hm f hf).jumps b hb _ ho hT args k hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hvf hb hi hold hT hres hk
        have hhp := ih n (Nat.lt_succ_self n) f hf tgt htm 0 env'
          (List.length_pos_iff.2 (hvf.blocksNonEmpty tgt htm)) hold'
        rw [List.drop_zero] at hhp
        refine HasPath.bind_ok (a := (tgt, env')) ?_ hhp
        rw [hj]
        rfl
    · rename_i hT
      have hTf : isTerminator b.body[i].op = false := by simpa using hT
      split
      · refine HasPath.bind_lift (htot.1 hTf) fun rs _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        refine HasPath.bind_ok ?_ (ih n (Nat.lt_succ_self n) f hf b hb (i + 1) _ (hnext hTf)
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
        have hhp := ih n (Nat.lt_succ_self n) g hgm e hem 0 _
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

/-- No path of a run of a function of the module `M` is stuck, at any
budget, on any argument vector, calls and recursion included, when every
function of `M` is valid and runs within `M`. -/
theorem Func.neverStuck_of_inModule (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M) {f : Func d} (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.runs M args) := by
  intro n ⟨st, h⟩
  have hvf := hv f hf
  obtain ⟨e, he, hep⟩ := hvf.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hns := Module.calls_noStuck hv hm n f hf e hmem 0 _
    (List.length_pos_iff.2 (hvf.blocksNonEmpty e hmem)) (Env.scoped_params hvf he hep args)
  rw [List.drop_zero] at hns
  rcases (Func.run_run M f args n _).1 h with ⟨p, hp, e', he', hd⟩ | ⟨_, hst, _⟩
  · rw [Func.enter_entry he hep] at hp
    cases hp
    match e', he', hd with
    | .ok (.error st'), he', _ => exact hns st' he'
    | .ok (.ok (.ret _)), _, hd | .ok (.ok .fuelExhausted), _, hd | .ub _, _, hd => cases hd
  · rw [Func.enter_entry he hep] at hst
    cases hst

/-- A run of a function of the module `M` has an outcome at every budget,
on any argument vector, calls and recursion included, when every function
of `M` is valid and runs within `M`, and every op of `M` is total. -/
theorem Func.progress_of_inModule (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M)
    (ht : ∀ g ∈ M.funcs, ∀ b ∈ g.blocks, ∀ o ∈ b.body, OpTotal o.op) {f : Func d}
    (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    Progress (f.runs M args) := by
  intro n
  have hvf := hv f hf
  obtain ⟨e, he, hep⟩ := hvf.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hpos := List.length_pos_iff.2 (hvf.blocksNonEmpty e hmem)
  have hold := Env.scoped_params hvf he hep args
  obtain ⟨ev, hev⟩ := Module.calls_hasPath hv hm ht n f hf e hmem 0 _ hpos hold
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
