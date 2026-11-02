import Fir.Execution.Environment
import Fir.Execution.Monotone
import Fir.Execution.Propagation
import Fir.Validation.Rules

/-!
# Progress and no stuck path, for functions that run straight

A valid function's run is never stuck, and has an outcome at every budget,
when its ops run straight to a return: no op calls a function, and each
terminator returns, never jumps, and returns values of the function's
result types (`Func.Straight`). The tracer subset of #10, `const`, `add`
without flags and `ret`, is such a set of ops. Branches and calls need
more: a jump lands in a block whose values are defined on another path,
and a call runs another function. The next two sections extend these
theorems to jumps and loops (`Func.neverStuck_of_local`,
`Func.progress_of_local`), and the sections after them to calls and
recursion (`Func.neverStuck_of_inModule`, `Func.progress_of_inModule`).

The proof follows the run through the entry block, the only block that
such a function runs. Before its op at index `i`, the run's environment
holds, for each parameter and each result of the ops before `i`, a value
of the type that the function gives it (`Env.Holds`). Validation makes
each operand of the op one of those names: the only definitions that
dominate a use in the entry block are the parameters and the results of
the ops before it. So the operands are found with their types, the op's
results bind, and the invariant holds before the next op. The other
checks pass by the rules of validation: no op owns a region, an op that is
not a terminator has a next op, and nothing follows the terminator.

`NeverStuck` needs nothing of the ops' semantics beyond that: an op that
may end in many ways is never stuck in any of them. `Progress` needs each
op to be total (`OpTotal`), so that each step has a way to go on.
-/

namespace Fir

open SetM

/-! # Functions that run straight -/

section

variable {d : Dialect}

/-- A list with a head is that head and a tail. -/
theorem eq_cons_of_head? {l : List α} {a : α} (h : l.head? = some a) : ∃ t, l = a :: t := by
  cases l with
  | nil => cases h
  | cons b t => cases h; exact ⟨t, rfl⟩

/-- The definitions of a function start with its parameters, then its
entry block's arguments and the results of its entry block's ops. -/
theorem Func.defs_entry {f : Func d} {e : Block d} (he : f.blocks.head? = some e) :
    ∃ rest, f.defs = f.params ++ (e.params ++ e.body.flatMap (·.results)) ++ rest := by
  obtain ⟨t, ht⟩ := eq_cons_of_head? he
  obtain ⟨l, ps, body⟩ := e
  exact ⟨(Operation.regionBlocks body ++ Block.allBlocks t).flatMap Block.defs, by
    simp only [Func.defs, Func.allBlocks, ht, Block.allBlocks, List.cons_append,
      List.flatMap_cons, Block.defs, List.append_assoc]⟩

/-- What the entry block `e` of `f` has defined before its op at index
`i`: the parameters, and the results of the ops before it. -/
def Func.defsBefore (f : Func d) (e : Block d) (i : Nat) : List (Name × d.Ty) :=
  f.params ++ (e.body.take i).flatMap (·.results)

end

section

variable {d : Dialect} [DialectSignature d] [DialectValidation d] {ctx : ModuleContext d}
  {f : Func d} {e : Block d}

/-- In a valid function, an op of the entry block uses only the
parameters and the results of the ops before it: no other definition
dominates it. -/
theorem Func.mem_defsBefore (hv : f.Valid ctx) (he : f.blocks.head? = some e)
    (hep : e.params = []) {i : Nat} {x : Name} (hx : f.InScope x e.label i) :
    x ∈ (f.defsBefore e i).map (·.1) := by
  obtain ⟨t, ht⟩ := eq_cons_of_head? he
  have hentry : f.entryLabel? = some e.label := by simp [Func.entryLabel?, he]
  have hsame : ∀ b ∈ f.blocks, b.label = e.label → b = e := by
    intro b hb hl
    have hnd := hv.labelsUnique
    rw [ht] at hb hnd
    rcases List.mem_cons.1 hb with rfl | hb
    · rfl
    · rw [List.map_cons, List.nodup_cons] at hnd
      exact absurd (hl ▸ List.mem_map.2 ⟨b, hb, rfl⟩) hnd.1
  have hdom : ∀ a, f.Dominates a e.label → a = e.label := by
    intro a h
    rcases h with h | h
    · exact h
    · by_cases ha : a = e.label
      · exact ha
      · exact absurd (Func.ReachesAvoiding.entry hentry (Ne.symm ha)) h
  obtain ⟨⟨s, hs⟩, hall⟩ := hx
  have hd := hall s hs
  simp only [Func.defsBefore, List.map_append, List.mem_append]
  cases s with
  | param => exact .inl hs
  | arg a =>
    obtain ⟨b, hb, hl, hx⟩ := hs
    have hbe := hsame b hb (hl.trans (hdom a hd))
    subst hbe
    rw [hep] at hx
    cases hx
  | result a j =>
    obtain ⟨b, hb, hl, o', ho', hx⟩ := hs
    rcases hd with ⟨ha, hj⟩ | ⟨ha, hd⟩
    · have hbe := hsame b hb (hl.trans ha)
      subst hbe
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have hto : (b.body.take i)[j]? = some o' := by rw [List.getElem?_take, ite_eq_left hj, ho']
      exact .inr (List.mem_map.2 ⟨p, List.mem_flatMap.2 ⟨o', List.mem_of_getElem? hto, hp⟩, rfl⟩)
    · exact absurd (hdom a hd) ha

/-- The results of the entry block's op at index `i` are defined in `f`,
with their types, and none of them is defined before that op. -/
theorem Func.results_fresh (hv : f.Valid ctx) (he : f.blocks.head? = some e)
    (hep : e.params = []) {i : Nat} (hi : i < e.body.length) :
    (∀ p ∈ e.body[i].results, f.typeOf p.1 = some p.2) ∧
      ∀ x ∈ (f.defsBefore e i).map (·.1), x ∉ e.body[i].results.map (·.1) := by
  obtain ⟨rest, hdefs⟩ := Func.defs_entry he
  have hsplit : e.body.flatMap (·.results) = (e.body.take i).flatMap (·.results) ++
      (e.body[i].results ++ (e.body.drop (i + 1)).flatMap (·.results)) := by
    conv => lhs; rw [← List.take_append_drop i e.body, List.drop_eq_getElem_cons hi]
    simp only [List.flatMap_append, List.flatMap_cons]
  have hnd := hv.namesUnique
  rw [hdefs, hep, List.nil_append, hsplit] at hnd
  have hA : ((f.defsBefore e i).map (·.1) ++ e.body[i].results.map (·.1)).Nodup := by
    refine List.Nodup.sublist ?_ hnd
    simp only [Func.defsBefore, List.map_append, List.append_assoc]
    exact ((List.sublist_append_left _ _).append_left _).append_left _
  refine ⟨fun p hp => Func.typeOf_of_mem hv.namesUnique ?_, ?_⟩
  · rw [hdefs, hep, List.nil_append, hsplit]
    simp [hp]
  · intro x hx hx'
    exact (List.nodup_append.1 hA).2.2 x hx x hx' rfl

end

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectValidation d] {ctx : ModuleContext d} {f : Func d} {e : Block d}

omit [DecidableEq d.Ty] in
/-- After the entry block's op at index `i` binds its results, the
environment holds every name defined before the next op. -/
theorem Func.holds_next (hv : f.Valid ctx) (he : f.blocks.head? = some e) (hep : e.params = [])
    {i : Nat} (hi : i < e.body.length) {env : Env d}
    (hold : env.Holds f ((f.defsBefore e i).map (·.1)))
    (rs : HVector toType (returnTypes e.body[i].op))
    (hrty : e.body[i].results.map (·.2) = returnTypes e.body[i].op) :
    Env.Holds ((e.body[i].results.map (·.1)).zip rs.toDVals ++ env) f
      ((f.defsBefore e (i + 1)).map (·.1)) := by
  obtain ⟨hdef, hfresh⟩ := Func.results_fresh hv he hep hi
  have h := Env.holds_bind hold ((HVector.toDVals_types rs).trans hrty.symm) hdef hfresh
  have hdb : f.defsBefore e (i + 1) = f.defsBefore e i ++ e.body[i].results := by
    simp only [Func.defsBefore, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rw [hdb, List.map_append]
  exact h

/-- What a run needs of the entry block's op at index `i`: no region,
operands found with their types, results of the op's result types, and a
next op exactly when it is not a terminator. -/
theorem Func.op_ready (hv : f.Valid ctx) (he : f.blocks.head? = some e) (hep : e.params = [])
    {i : Nat} (hi : i < e.body.length) {env : Env d}
    (hold : env.Holds f ((f.defsBefore e i).map (·.1))) :
    e.body[i].regions = [] ∧
      (∃ args : HVector toType (sig e.body[i].op),
        env.operands (sig e.body[i].op) e.body[i].operands = .ok args) ∧
      e.body[i].results.map (·.2) = returnTypes e.body[i].op ∧
      (isTerminator e.body[i].op = true → e.body.drop (i + 1) = []) ∧
      (isTerminator e.body[i].op = false → i + 1 < e.body.length) := by
  obtain ⟨t, ht⟩ := eq_cons_of_head? he
  have hmem : e ∈ f.blocks := ht ▸ List.mem_cons_self
  obtain ⟨hreg, hoty, hrty, hterm, -, -, -, hscope, -⟩ :=
    hv.ops e hmem i e.body[i] (List.getElem?_eq_getElem hi)
  refine ⟨hreg, Env.operands_ok _ _ hoty fun x hx =>
    hold x (Func.mem_defsBefore hv he hep (hscope x (List.mem_append_left _ hx))), hrty,
    fun hT => List.drop_eq_nil_of_le (by have := hterm.1 hT; omega), fun hT => ?_⟩
  have hne : i + 1 ≠ e.body.length := fun h => by rw [hterm.2 h] at hT; cases hT
  omega

end

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- The ops of `f` run straight to a return: no op calls a function, and
each terminator returns, never jumps, and returns values of `f`'s result
types. -/
structure Func.Straight (f : Func d) : Prop where
  noCall : ∀ b ∈ f.blocks, ∀ o ∈ b.body, callee? o.op = none
  noJump : ∀ b ∈ f.blocks, ∀ o ∈ b.body, ∀ args i,
    ¬ DialectDenote.exit (m := SetM) o.op args (.ok (.goto i))
  returns : ∀ b ∈ f.blocks, ∀ o ∈ b.body, isTerminator o.op = true → sig o.op = f.results

variable [DialectValidation d] {ctx : ModuleContext d} {f : Func d} {e : Block d}

/-- No path of a run of the entry block of a function that runs straight
is stuck, from any op on, with an environment that holds what was defined
before it. -/
theorem Func.straight_noStuck (hv : f.Valid ctx) (hs : f.Straight) (he : f.blocks.head? = some e)
    (hep : e.params = []) (M : Module d) (n : Nat) :
    ∀ (i : Nat) (env : Env d), i < e.body.length →
      env.Holds f ((f.defsBefore e i).map (·.1)) →
      NoStuck (Func.runOps (m := SetM) M n f env (e.body.drop i)) := by
  obtain ⟨t, ht⟩ := eq_cons_of_head? he
  have hmem : e ∈ f.blocks := ht ▸ List.mem_cons_self
  induction n with
  | zero => intro i env _ _; simp only [Func.runOps]; exact NoStuck.pure'
  | succ n ih =>
    intro i env hi hold
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready hv he hep hi hold
    rw [List.drop_eq_getElem_cons hi]
    simp only [Func.runOps]
    rw [ite_eq_right (by simp [hreg])]
    refine NoStuck.bind ?_ fun args' _ => ?_
    · rw [hargs]; exact NoStuck.liftExcept_ok
    split
    · rename_i hT
      rw [ite_eq_right (by simp [hlast hT])]
      refine NoStuck.bind NoStuck.lift fun x hx => ?_
      have hex : DialectDenote.exit (m := SetM) e.body[i].op args' (.ok x) := by
        rcases (run_lift _ _).1 hx with ⟨_, h, he'⟩ | ⟨_, _, he'⟩
        · cases he'; exact h
        · cases he'
      cases x with
      | ret => rw [ite_eq_left (hs.returns e hmem _ ho hT)]; exact NoStuck.pure'
      | goto j => exact absurd hex (hs.noJump e hmem _ ho args' j)
    · rename_i hT
      split
      · refine NoStuck.bind NoStuck.lift fun rs _ => ?_
        have hlen : (e.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        refine NoStuck.bind ?_ fun env' henv' => ?_
        · rw [Env.bind_ok _ _ hlen]; exact NoStuck.liftExcept_ok
        rw [Env.bind_ok _ _ hlen] at henv'
        cases (run_liftExcept _ _).1 henv'
        exact ih (i + 1) _ (hnext (by simpa using hT)) (Func.holds_next hv he hep hi hold rs hrty)
      · rename_i heq
        rw [hs.noCall e hmem _ ho] at heq
        cases heq

/-- A run of the entry block of a function that runs straight, and whose
ops are total, has a path, from any op on, with an environment that holds
what was defined before it. -/
theorem Func.straight_hasPath (hv : f.Valid ctx) (hs : f.Straight)
    (ht : ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpTotal o.op) (he : f.blocks.head? = some e)
    (hep : e.params = []) (M : Module d) (n : Nat) :
    ∀ (i : Nat) (env : Env d), i < e.body.length →
      env.Holds f ((f.defsBefore e i).map (·.1)) →
      HasPath (Func.runOps (m := SetM) M n f env (e.body.drop i)) := by
  obtain ⟨t, hbt⟩ := eq_cons_of_head? he
  have hmem : e ∈ f.blocks := hbt ▸ List.mem_cons_self
  induction n with
  | zero => intro i env _ _; simp only [Func.runOps]; exact HasPath.pure'
  | succ n ih =>
    intro i env hi hold
    have ho := List.getElem_mem hi
    obtain ⟨hreg, ⟨args, hargs⟩, hrty, hlast, hnext⟩ := Func.op_ready hv he hep hi hold
    have htot := ht e hmem _ ho args
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
      | ret => rw [ite_eq_left (hs.returns e hmem _ ho hT)]; exact HasPath.pure'
      | goto j => exact absurd hex (hs.noJump e hmem _ ho args j)
    · rename_i hT
      split
      · refine HasPath.bind_lift (htot.1 (by simpa using hT)) fun rs _ => ?_
        have hlen : (e.body[i].results.map (·.1)).length = rs.toDVals.length := by
          have h1 := congrArg List.length (HVector.toDVals_types rs)
          have h2 := congrArg List.length hrty
          simp only [List.length_map] at h1 h2 ⊢
          omega
        refine HasPath.bind_ok ?_ (ih (i + 1) _ (hnext (by simpa using hT))
          (Func.holds_next hv he hep hi hold rs hrty))
        rw [Env.bind_ok _ _ hlen]
        rfl
      · rename_i heq
        rw [hs.noCall e hmem _ ho] at heq
        cases heq

omit [DialectSignature d] [DialectCall d] [DialectDenote d SetM] [DialectValidation d] in
/-- A run starts at the entry block of a function whose entry block
declares no arguments, with its parameters bound to the arguments. -/
theorem Func.enter_entry (he : f.blocks.head? = some e) (hep : e.params = [])
    (args : HVector toType (f.params.map (·.2))) :
    f.enter args.toDVals = .ok (e.body, (f.params.map (·.1)).zip args.toDVals) := by
  simp [Func.enter, he, hep, HVector.toDVals_types]
  rfl

omit [DecidableEq d.Ty] [DialectCall d] [DialectDenote d SetM] in
/-- The parameters, bound to arguments of their types, are what a run of
a valid function holds before its first op. -/
theorem Func.holds_params (hv : f.Valid ctx) (args : HVector toType (f.params.map (·.2))) :
    Env.Holds ((f.params.map (·.1)).zip args.toDVals) f ((f.defsBefore e 0).map (·.1)) := by
  have h := Env.holds_bind (env := []) (f := f) (xs := []) (fun _ h => nomatch h)
    (HVector.toDVals_types args)
    (fun p hp => Func.typeOf_of_mem hv.namesUnique (List.mem_append_left _ hp))
    (fun _ h => nomatch h)
  simpa [Func.defsBefore] using h

/-- No path of a run of a valid function that runs straight is stuck, at
any budget, on any argument vector. -/
theorem Func.neverStuck (hv : f.Valid ctx) (hs : f.Straight) (M : Module d)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.runs M args) := by
  intro n ⟨st, h⟩
  obtain ⟨e, he, hep⟩ := hv.entry
  obtain ⟨t, hbt⟩ := eq_cons_of_head? he
  have hpos : 0 < e.body.length := Nat.pos_of_ne_zero fun h =>
    hv.blocksNonEmpty e (hbt ▸ List.mem_cons_self) (List.eq_nil_of_length_eq_zero h)
  have hns := Func.straight_noStuck hv hs he hep M n 0 _ hpos (Func.holds_params hv args)
  rw [List.drop_zero] at hns
  rcases (Func.run_run M f args n _).1 h with ⟨p, hp, e', he', hd⟩ | ⟨_, hst, _⟩
  · rw [Func.enter_entry he hep] at hp
    cases hp
    match e', he', hd with
    | .ok (.error st'), he', _ => exact hns st' he'
    | .ok (.ok (.ret _)), _, hd | .ok (.ok .fuelExhausted), _, hd | .ub _, _, hd => cases hd
  · rw [Func.enter_entry he hep] at hst
    cases hst

/-- A run of a valid function that runs straight, and whose ops are
total, has an outcome at every budget, on any argument vector. -/
theorem Func.progress (hv : f.Valid ctx) (hs : f.Straight)
    (ht : ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpTotal o.op) (M : Module d)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.runs M args) := by
  intro n
  obtain ⟨e, he, hep⟩ := hv.entry
  obtain ⟨t, hbt⟩ := eq_cons_of_head? he
  have hpos : 0 < e.body.length := Nat.pos_of_ne_zero fun h =>
    hv.blocksNonEmpty e (hbt ▸ List.mem_cons_self) (List.eq_nil_of_length_eq_zero h)
  have hold := Func.holds_params (e := e) hv args
  obtain ⟨ev, hev⟩ := Func.straight_hasPath hv hs ht he hep M n 0 _ hpos hold
  have hns := Func.straight_noStuck hv hs he hep M n 0 _ hpos hold
  rw [List.drop_zero] at hev hns
  have hrun := (Func.run_run M f args n ev.dropLeft).2
    (.inl ⟨_, Func.enter_entry he hep args, ev, hev, rfl⟩)
  match ev, hev, hrun with
  | .ok (.ok (.ret (vs, _))), _, hrun => exact ⟨.ret vs, hrun⟩
  | .ok (.ok .fuelExhausted), _, hrun => exact ⟨.fuelExhausted, hrun⟩
  | .ub r, _, hrun => exact ⟨.ub r, hrun⟩
  | .ok (.error st), hev, _ => exact absurd hev (hns st)

end Fir
