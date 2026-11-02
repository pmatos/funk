import Fir.Execution.Scoped
import Fir.Execution.Progress

/-!
# Progress and no stuck path, with jumps and loops

A valid function's run is never stuck, and has an outcome at every budget,
when the function runs within itself (`Func.Local`): no op calls a
function, and its terminators keep to the rules that validation makes of
them.

* A terminator that jumps names a successor that it has, and gives no
  results, since the interpreter binds none for it.
* A terminator that returns returns values of the function's result types.

Branches and loops are included: a run may jump to any block, as often as
its fuel allows. A function that runs straight (`Func.Straight`) runs
within itself (`Func.Straight.local`), so these theorems extend those of
the section on progress and no stuck path. Calls are left to #20, whose
callee runs another function.

The proof is by induction on the budget, from any op of any block of the
function on. Its invariant is `Env.Scoped`: before an op, the environment
holds a value of its type for each value in scope at the op. So the op's
operands are found with their types, and the other checks pass by the
rules of validation, as for a function that runs straight. On a jump, the
values that the successor passes are in scope too, so they are found, and
they have the types of the target block's arguments, by validation. The
invariant then holds at the target's first op (the section on the values
in scope at each op), and the run goes on there with one step less.

`NeverStuck` needs nothing more of the ops' semantics. `Progress` needs
each op to be total (`OpTotal`), so that each step has a way to go on.
-/

namespace Fir

open SetM

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty]

omit [DecidableEq d.Ty] in
/-- The values of names that the environment holds are found, each with
the type that the function gives its name. -/
theorem Env.mapM_value_ok {env : Env d} {f : Func d} :
    ∀ {xs : List Name}, env.Holds f xs →
      ∃ vs, xs.mapM env.value = .ok vs ∧ xs.map f.typeOf = (vs.map (·.1)).map some
  | [], _ => ⟨[], rfl, rfl⟩
  | x :: xs, hold => by
    obtain ⟨dv, hl, hty⟩ := hold x List.mem_cons_self
    obtain ⟨vs, hvs, htys⟩ := Env.mapM_value_ok fun y hy => hold y (List.mem_cons_of_mem _ hy)
    refine ⟨dv :: vs, ?_, by simp [hty, htys]⟩
    simp only [List.mapM_cons, Env.value, hl, hvs]
    rfl

variable [DialectSignature d] [DialectValidation d] {ctx : ModuleContext d} {f : Func d}
  {b : Block d}

/-- What a run needs of the op at index `i` of a block: no region, operands
found with their types, results of the op's result types, and a next op
exactly when it is not a terminator. -/
theorem Func.op_ready_of_scoped (hv : f.Valid ctx) (hb : b ∈ f.blocks) {i : Nat}
    (hi : i < b.body.length) {env : Env d} (hold : env.Scoped f b.label i) :
    b.body[i].regions = [] ∧
      (∃ args : HVector toType (sig b.body[i].op),
        env.operands (sig b.body[i].op) b.body[i].operands = .ok args) ∧
      b.body[i].results.map (·.2) = returnTypes b.body[i].op ∧
      (isTerminator b.body[i].op = true → b.body.drop (i + 1) = []) ∧
      (isTerminator b.body[i].op = false → i + 1 < b.body.length) := by
  obtain ⟨hreg, hoty, hrty, hterm, -, -, -, hscope, -⟩ :=
    hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)
  refine ⟨hreg, Env.operands_ok _ _ hoty
    (hold.holds fun x hx => hscope x (List.mem_append_left _ hx)), hrty,
    fun hT => List.drop_eq_nil_of_le (by have := hterm.1 hT; omega), fun hT => ?_⟩
  have hne : i + 1 ≠ b.body.length := fun h => by rw [hterm.2 h] at hT; cases hT
  omega

omit [DecidableEq d.Ty] in
/-- After the op at index `i` of a block binds its results, the
environment holds every value in scope at the next op. -/
theorem Func.scoped_next (hv : f.Valid ctx) (hb : b ∈ f.blocks) {i : Nat}
    (hi : i < b.body.length) {env : Env d} (hold : env.Scoped f b.label i)
    (rs : HVector toType (returnTypes b.body[i].op))
    (hrty : b.body[i].results.map (·.2) = returnTypes b.body[i].op) :
    Env.Scoped ((b.body[i].results.map (·.1)).zip rs.toDVals ++ env) f b.label (i + 1) :=
  Env.scoped_bind ((HVector.toDVals_types rs).trans hrty.symm)
    (fun _ hp => Func.typeOf_of_mem hv.namesUnique
      (Func.mem_defs_result hb (List.getElem_mem hi) hp))
    (fun x hx hnot => hold x (Func.inScope_of_next hv hb hi hx hnot))

/-- A terminator with no results that jumps to a successor it has finds
the block that the successor names, and the values it passes, of the
types of that block's arguments; the environment then holds every value
in scope at that block's first op. -/
theorem Func.jump_ok (hv : f.Valid ctx) (hb : b ∈ f.blocks) {i : Nat} (hi : i < b.body.length)
    {env : Env d} (hold : env.Scoped f b.label i) (hT : isTerminator b.body[i].op = true)
    (hres : returnTypes b.body[i].op = []) {k : Nat} (hk : k < succCount b.body[i].op) :
    ∃ tgt env', f.jump env b.body[i].succs k = .ok (tgt, env') ∧ tgt ∈ f.blocks ∧
      env'.Scoped f tgt.label 0 := by
  have ho := List.getElem?_eq_getElem hi
  obtain ⟨-, -, hrty, hterm, hcount, -, hsucc, hscope, -⟩ := hv.ops b hb i b.body[i] ho
  have hks : k < b.body[i].succs.length := hcount ▸ hk
  have hsm : b.body[i].succs[k] ∈ b.body[i].succs := List.getElem_mem hks
  obtain ⟨-, tgt, htgt, hty⟩ := hsucc _ hsm
  obtain ⟨htm, hlab⟩ := Func.block?_some htgt
  obtain ⟨vs, hvs, hvty⟩ := Env.mapM_value_ok (env := env) (f := f)
    (xs := b.body[i].succs[k].args) (hold.holds fun x hx => hscope x
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hsm, hx⟩)))
  have htys : vs.map (·.1) = tgt.params.map (·.2) := by
    have h : (vs.map (·.1)).map some = (tgt.params.map (·.2)).map some := by
      rw [← hvty, hty, List.map_map]
      rfl
    exact (List.map_inj_right fun _ _ h => Option.some.inj h).1 h
  have hlen : (tgt.params.map (·.1)).length = vs.length := by
    rw [List.length_map, ← List.length_map (f := (·.2)), ← htys, List.length_map]
  have hresults : b.body[i].results = [] := List.map_eq_nil_iff.1 (hrty.trans hres)
  refine ⟨tgt, _, ?_, htm, Env.scoped_bind htys
    (fun _ hp => Func.typeOf_of_mem hv.namesUnique (Func.mem_defs_arg htm hp))
    (fun x hx hnot => hold x (Func.inScope_of_jump hv hb htm ho (hterm.1 hT) hresults hsm
      hlab hx hnot))⟩
  have hok : ∀ {α β : Type} (a : α) (g : α → Except Stuck β), (Except.ok a >>= g) = g a :=
    fun _ _ => rfl
  simp only [Func.jump, List.getElem?_eq_getElem hks, htgt, hvs, hok, Env.bind_ok _ _ hlen, htys]
  rfl

end

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- The ops of `f` run within `f`: no op calls a function; a terminator
that jumps names a successor that it has, and gives no results; and a
terminator that returns returns values of `f`'s result types. -/
structure Func.Local (f : Func d) : Prop where
  noCall : ∀ b ∈ f.blocks, ∀ o ∈ b.body, callee? o.op = none
  jumps : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → ∀ args i,
    DialectDenote.exit (m := SetM) o.op args (.ok (.goto i)) →
      i < succCount o.op ∧ returnTypes o.op = []
  returns : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → ∀ args,
    DialectDenote.exit (m := SetM) o.op args (.ok .ret) → sig o.op = f.results

omit [DecidableEq d.Ty] in
/-- A function that runs straight runs within itself. -/
theorem Func.Straight.local {f : Func d} (hs : f.Straight) : f.Local where
  noCall := hs.noCall
  jumps b hb o ho _ args i h := absurd h (hs.noJump b hb o ho args i)
  returns b hb o ho hT _ _ := hs.returns b hb o ho hT

variable [DialectValidation d] {ctx : ModuleContext d} {f : Func d}

omit [DecidableEq d.Ty] [DialectCall d] [DialectValidation d] in
/-- A way that the exit of an op, lifted into the run, ends with a place to
go is a way that the exit ends. -/
theorem exit_of_lift {op : d.Op} {args : HVector toType (sig op)} {x : Exit}
    (hx : (ExceptT.lift (DialectDenote.exit (m := SetM) op args) : ExceptT Stuck SetM Exit).run
      (.ok (.ok x))) : DialectDenote.exit (m := SetM) op args (.ok x) := by
  rcases (run_lift _ _).1 hx with ⟨_, h, he⟩ | ⟨_, _, he⟩
  · cases he; exact h
  · cases he

/-- No path of a run of a local function is stuck, from any op of any of
its blocks on, with an environment that holds the values in scope there. -/
theorem Func.local_noStuck (hv : f.Valid ctx) (hl : f.Local) (M : Module d) (n : Nat) :
    ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → NoStuck (Func.runOps (m := SetM) M n f env (b.body.drop i)) := by
  induction n with
  | zero => intro _ _ _ _ _ _; simp only [Func.runOps]; exact NoStuck.pure'
  | succ n ih =>
    intro b hb i env hi hold
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hv hb hi hold
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
      | ret => rw [ite_eq_left (hl.returns b hb _ ho hT args' hex)]; exact NoStuck.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := hl.jumps b hb _ ho hT args' k hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hv hb hi hold hT hres hk
        refine NoStuck.bind ?_ fun p hp => ?_
        · rw [hj]; exact NoStuck.liftExcept_ok
        rw [hj] at hp
        cases (run_liftExcept _ _).1 hp
        have hns := ih tgt htm 0 env'
          (List.length_pos_iff.2 (hv.blocksNonEmpty tgt htm)) hold'
        rwa [List.drop_zero] at hns
    · rename_i hT
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
        exact ih b hb (i + 1) _ (hnext (by simpa using hT)) (Func.scoped_next hv hb hi hold rs hrty)
      · rename_i heq
        rw [hl.noCall b hb _ ho] at heq
        cases heq

/-- A run of a local function whose ops are total has a path, from any op
of any of its blocks on, with an environment that holds the values in
scope there. -/
theorem Func.local_hasPath (hv : f.Valid ctx) (hl : f.Local)
    (ht : ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpTotal o.op) (M : Module d) (n : Nat) :
    ∀ b ∈ f.blocks, ∀ (i : Nat) (env : Env d), i < b.body.length →
      env.Scoped f b.label i → HasPath (Func.runOps (m := SetM) M n f env (b.body.drop i)) := by
  induction n with
  | zero => intro _ _ _ _ _ _; simp only [Func.runOps]; exact HasPath.pure'
  | succ n ih =>
    intro b hb i env hi hold
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready_of_scoped hv hb hi hold
    have htot := ht b hb _ ho args
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
      | ret => rw [ite_eq_left (hl.returns b hb _ ho hT args hex)]; exact HasPath.pure'
      | goto k =>
        obtain ⟨hk, hres⟩ := hl.jumps b hb _ ho hT args k hex
        obtain ⟨tgt, env', hj, htm, hold'⟩ := Func.jump_ok hv hb hi hold hT hres hk
        have hhp := ih tgt htm 0 env' (List.length_pos_iff.2 (hv.blocksNonEmpty tgt htm)) hold'
        rw [List.drop_zero] at hhp
        refine HasPath.bind_ok (a := (tgt, env')) ?_ hhp
        rw [hj]
        rfl
    · rename_i hT
      split
      · refine HasPath.bind_lift (htot.1 (by simpa using hT)) fun rs _ => ?_
        have hlen : (b.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        refine HasPath.bind_ok ?_ (ih b hb (i + 1) _ (hnext (by simpa using hT))
          (Func.scoped_next hv hb hi hold rs hrty))
        rw [Env.bind_ok _ _ hlen]
        rfl
      · rename_i heq
        rw [hl.noCall b hb _ ho] at heq
        cases heq

/-- No path of a run of a valid local function is stuck, at any budget, on
any argument vector, jumps and loops included. -/
theorem Func.neverStuck_of_local (hv : f.Valid ctx) (hl : f.Local) (M : Module d)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.runs M args) := by
  intro n ⟨st, h⟩
  obtain ⟨e, he, hep⟩ := hv.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hns := Func.local_noStuck hv hl M n e hmem 0 _
    (List.length_pos_iff.2 (hv.blocksNonEmpty e hmem)) (Env.scoped_params hv he hep args)
  rw [List.drop_zero] at hns
  rcases (Func.run_run M f args n _).1 h with ⟨p, hp, e', he', hd⟩ | ⟨_, hst, _⟩
  · rw [Func.enter_entry he hep] at hp
    cases hp
    match e', he', hd with
    | .ok (.error st'), he', _ => exact hns st' he'
    | .ok (.ok (.ret _)), _, hd | .ok (.ok .fuelExhausted), _, hd | .ub _, _, hd => cases hd
  · rw [Func.enter_entry he hep] at hst
    cases hst

/-- A run of a valid local function whose ops are total has an outcome at
every budget, on any argument vector, jumps and loops included. -/
theorem Func.progress_of_local (hv : f.Valid ctx) (hl : f.Local)
    (ht : ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpTotal o.op) (M : Module d)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.runs M args) := by
  intro n
  obtain ⟨e, he, hep⟩ := hv.entry
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hpos := List.length_pos_iff.2 (hv.blocksNonEmpty e hmem)
  have hold := Env.scoped_params hv he hep args
  obtain ⟨ev, hev⟩ := Func.local_hasPath hv hl ht M n e hmem 0 _ hpos hold
  have hns := Func.local_noStuck hv hl M n e hmem 0 _ hpos hold
  rw [List.drop_zero] at hev hns
  have hrun := (Func.run_run M f args n ev.dropLeft).2
    (.inl ⟨_, Func.enter_entry he hep args, ev, hev, rfl⟩)
  match ev, hev, hrun with
  | .ok (.ok (.ret (vs, _))), _, hrun => exact ⟨.ret vs, hrun⟩
  | .ok (.ok .fuelExhausted), _, hrun => exact ⟨.fuelExhausted, hrun⟩
  | .ub r, _, hrun => exact ⟨.ub r, hrun⟩
  | .ok (.error st), hev, _ => exact absurd hev (hns st)

end Fir
