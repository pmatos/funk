import Fir.Execution.MemoryCalls

/-!
# Two modules with memory, compared call by call

The refinement theorems with memory compare the runs of a function in a
source module with its runs in a target module, as those for runs in the
set monad do (the section on two modules, compared call by call), but from
given memories, of which the target's refine the source's. Their proofs
share one engine. It follows a path of the target's run, and finds a way
that the source's run _allows_ it: the source hits UB at some budget, which
allows anything, or, for a return, returns at some budget values that the
target's refine, with memories that the target's refine.

Each op runs alike in both, on operands of which the target's refine the
source's, from memories of which the target's refine the source's: what it
does on them is allowed by what it does on the source's, since every op that
runs by its own rule is monotone with memory. A call runs its callee in a
frame, from the memories that its caller reached. Each symbol names, in
both, the same function, whose run the engine follows in turn, or a _black
box_: a function of the source and a function of the target, of the same
parameter types, such that

* on arguments that refine others, and from memories that refine others,
  the observable behaviour of the target's function, with the memories it
  ends with, refines that of the source's;
* its runs from given memories are _bounded_: on each argument vector and
  from each memories, the target's function diverges, or never runs out of
  fuel at any budget of at least a fixed bound.

The black box speaks of runs from any memories, not only of runs from the
empty memories: a callee runs from the memories its caller reached, and its
caller goes on from those it leaves.
-/

namespace Fir

open SetM Memory

section

variable {α : Type} [HRefinement α α]

/-- The source `src`, a run at each budget, allows the target's path: it
hits UB at some budget, which allows anything, or, for a return, it returns
at some budget what refines to the target's. A path that runs out of fuel
or is stuck asks nothing here. -/
def MemAllowed (src : Nat → ExceptT Stuck SetM (Result (α × Nat))) :
    Ev (Except Stuck (Result (α × Nat))) → Prop
  | .ok (.ok (.ret (a', _))) =>
    SomeUB src ∨ ∃ N a k, (src N).run (.ok (.ok (.ret (a, k)))) ∧ a ⊑ a'
  | .ub _ => SomeUB src
  | _ => True

variable {src c : Nat → ExceptT Stuck SetM (Result (α × Nat))}
  {e : Ev (Except Stuck (Result (α × Nat)))}

/-- UB at some budget allows every path. -/
theorem MemAllowed.of_someUB (h : SomeUB src) : ∀ e, MemAllowed src e
  | .ok (.ok (.ret _)) => .inl h
  | .ub _ => h
  | .ok (.ok .fuelExhausted) | .ok (.error _) => trivial

/-- A path that runs out of fuel or is stuck is allowed by every source. -/
theorem MemAllowed.of_not (h : ¬ (Ev.NotStuck e ∧ e ≠ .ok (.ok .fuelExhausted))) :
    MemAllowed src e := by
  match e with
  | .ok (.ok .fuelExhausted) | .ok (.error _) => trivial
  | .ok (.ok (.ret _)) => exact (h ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩).elim
  | .ub _ => exact (h ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩).elim

/-- A path allowed by the rest of a run is allowed by the whole, when every
way that the rest ends at the budget `N` is a way that the whole ends at
`N₀ + N + 1`, with `k` more steps left on a return. -/
theorem MemAllowed.of_step {k : Nat} (N₀ : Nat)
    (hstep : ∀ N x, Ev.NotStuck x → x ≠ .ok (.ok .fuelExhausted) → (c N).run x →
      (src (N₀ + N + 1)).run (x.addLeft k)) :
    MemAllowed c e → MemAllowed src e := by
  match e with
  | .ok (.ok .fuelExhausted) | .ok (.error _) => exact fun _ => trivial
  | .ub _ =>
    rintro ⟨N, r, h⟩
    exact ⟨_, r, hstep N (.ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩
  | .ok (.ok (.ret _)) =>
    rintro (⟨N, r, h⟩ | ⟨N, vs, i, h, hr⟩)
    · exact .inl ⟨_, r, hstep N (.ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩
    · exact .inr ⟨_, vs, i + k, hstep N (.ok (.ok (.ret (vs, i)))) (fun _ h => nomatch h)
        (fun h => nomatch h) h, hr⟩

end

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-! # A call's frame -/

/-- A path of a callee in the target's frame is allowed by the source's
callee in its frame, from memories that the target's refine, when each path
of the target's callee's ops, from the memories with a frame entered, is
allowed by the source's: leaving a frame keeps refinement. -/
theorem Func.memCall_allowed {M M' : Module d} {n : Nat} {g g' : Func d} {genv genv' : Env d}
    {body body' : List (Operation d)} {S S' : Memories Mem unit}
    (h : ∀ e₀, (Func.memOps M' n g' genv' body' S'.enter).run e₀ →
      MemAllowed (fun N => Func.memOps M N g genv body S.enter) e₀)
    {e' : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (he' : (Func.memCall M' n g' genv' body' S').run e') :
    MemAllowed (fun N => Func.memCall M N g genv body S) e' := by
  have ub : SomeUB (fun N => Func.memOps M N g genv body S.enter) →
      SomeUB (fun N => Func.memCall M N g genv body S) := fun ⟨N, r, h⟩ =>
    ⟨N, r, by
      show (Func.memCall M N g genv body S).run _
      rw [Func.memCall_eq]
      exact (SetM.run_map _ _ _).2 (.inr (.inr ⟨r, h, rfl⟩))⟩
  rw [Func.memCall_eq] at he'
  rcases (SetM.run_map _ _ _).1 he' with ⟨r, hr, rfl⟩ | ⟨_, _, rfl⟩ | ⟨r, hr, rfl⟩
  · match r, hr with
    | .fuelExhausted, _ => trivial
    | .ret ((vs', T'), k'), hr =>
      rcases h _ hr with hu | ⟨N, ⟨vs, T⟩, k, hx, hle⟩
      · exact .inl (ub hu)
      · refine .inr ⟨N, (vs, T.exit), k, ?_, hle.1, hle.2.exit⟩
        show (Func.memCall M N g genv body S).run _
        rw [Func.memCall_eq]
        exact (SetM.run_map _ _ _).2 (.inl ⟨_, hx, rfl⟩)
  · trivial
  · exact ub (h _ hr)

omit [TyRefinement d.Ty] in
/-- A caller whose callee returns at the budget `N₁`, and whose rest ends so
at the budget `N₂`, ends so at `N₁ + N₂ + 1`, leaving the callee's steps
too. -/
theorem Func.memCall_cont {M : Module d} {f g : Func d} {env genv : Env d} {o : Operation d}
    {os body : List (Operation d)} {args : HVector toType (sig o.op)} {s : Name}
    {vs : List (DVal d)} {S T : Memories Mem unit} {k N₁ N₂ : Nat}
    {x : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (hreg : o.ownsCoreRegion = false) (hargs : env.operands (sig o.op) o.operands = .ok args)
    (hT : isTerminator o.op = false) (hc : callee? o.op = some s) (hg : M.func? s = some g)
    (hen : g.enter args.toDVals = .ok (body, genv))
    (hx : (Func.memCall M N₁ g genv body S).run (.ok (.ok (.ret ((vs, T), k)))))
    (hty : vs.map (·.1) = returnTypes o.op) (hlen : (o.results.map (·.1)).length = vs.length)
    (hne : Ev.NotStuck x) (hxe : x ≠ .ok (.ok .fuelExhausted))
    (hcont : (Func.memOps M N₂ f ((o.results.map (·.1)).zip vs ++ env) os T).run x) :
    (Func.memOps M (N₁ + N₂ + 1) f env (o :: os) S).run (x.addLeft k) := by
  have hk := Func.memCall_left_le M N₁ g genv body S _ _ hx
  have hne' : Ev.NotStuck (x.addLeft k) := by
    intro st h
    match x, h with
    | .ok (.error _), _ => exact hne _ rfl
  refine (Func.memStepPath_iff hne').2 (.callRet hreg hargs hT hc hg hen
    ((Func.memCall_ahead M N₁ N₂ g genv body S).up_ret _ _ hx) hty hlen ?_)
  rw [Nat.min_eq_left (Nat.add_le_add_right hk _), Nat.add_comm k]
  have ha := Func.runOps_memAhead M N₂ k f ((o.results.map (·.1)).zip vs ++ env) os T
  match x, hcont with
  | .ok (.ok (.ret (a, i))), h => exact ha.up_ret _ _ h
  | .ub r, h => exact ha.up_ub _ h
  | .ok (.ok .fuelExhausted), _ => exact absurd rfl hxe
  | .ok (.error st), _ => exact absurd rfl (hne st)

/-! # Black boxes -/

/-- The runs `f` are bounded by the budget `B` when, on each input, they
diverge, or none of them with `B` steps or more runs out of fuel. -/
def FuncRuns.BoundedBy {A O : Type} (f : FuncRuns A O) (B : Nat) : Prop :=
  ∀ a, (∀ m, (f a m).outcomes .fuelExhausted) ∨ ∀ m, B ≤ m → ¬ (f a m).outcomes .fuelExhausted

/-- A black box with memory: the function `g` of the source module `M`,
whose calls the target module `M'` runs as calls of `g'`. Their parameters
have the same types; on arguments that refine others, from memories that
refine others, the behaviour of `g'` refines that of `g`, the memories they
end with included; and the runs of `g'` from given memories are bounded by
`bound`. -/
structure MemBlackBox (M M' : Module d) (bound : Nat) (g g' : Func d) : Prop where
  params : g'.params.map (·.2) = g.params.map (·.2)
  refines : ∀ (a a' : HVector toType (g.params.map (·.2))) (S S' : Memories Mem unit),
    a.Forall₂ TyRefinement.IsRefinedBy a' → S ⊑ S' →
      observable (g.memRunsFrom M (a, S)) ⊑ observable (g'.memRunsFrom M' (a'.cast params.symm, S'))
  bounded : (g'.memRunsFrom (Mem := Mem) (unit := unit) M').BoundedBy bound

variable (Mem unit) in
/-- The target module `M'` runs each call with memory as the source `M`
does: each symbol names the same function in both, or a black box with
memory. -/
def MemCallsRefined (M M' : Module d) (bound : Nat) : Prop :=
  ∀ s, M'.func? s = M.func? s ∨
    ∃ g g', M.func? s = some g ∧ M'.func? s = some g' ∧ MemBlackBox (Mem := Mem) (unit := unit)
      M M' bound g g'

/-- A call that enters a black box's target passes arguments of the
parameter types of the black box's source. -/
theorem MemBlackBox.sig {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : MemBlackBox (Mem := Mem) (unit := unit) M M' bound g g') {ts : List d.Ty}
    {args' : HVector toType ts} {p : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p) : ts = g.params.map (·.2) := by
  obtain ⟨_, _, _, hty', _⟩ := Func.enter_eq_ok hen'
  rw [HVector.toDVals_types] at hty'
  exact hty'.trans bb.params

/-- A path of a black box's target in its frame that is not stuck is a path
of its run from given memories, on the arguments cast to its parameter
types. -/
theorem MemBlackBox.target_run {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : MemBlackBox (Mem := Mem) (unit := unit) M M' bound g g') {ts : List d.Ty}
    {args' : HVector toType ts} {p' : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p') {S' : Memories Mem unit} {m : Nat}
    {x : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (hx : Ev.NotStuck x) (h : (Func.memCall M' m g' p'.2 p'.1 S').run x) :
    (g'.memRunsFrom M' ((args'.cast (bb.sig hen')).cast bb.params.symm, S') m) x.dropLeft := by
  have hen'' : g'.enter ((args'.cast (bb.sig hen')).cast bb.params.symm).toDVals = .ok p' := by
    rw [HVector.toDVals_cast, HVector.toDVals_cast]; exact hen'
  exact (Func.memRunsFrom_run (fun st hd => by
    match x, hd with
    | .ok (.error _), _ => exact hx _ rfl)).2 ⟨p', hen'', _, h, rfl⟩

omit [TyRefinement d.Ty] in
/-- A path of a function's run from given memories, on arguments cast to its
parameter types, that is not stuck is a path of its entry block's ops in a
frame, without the steps it leaves. -/
theorem Func.memRunsFrom_run_cast {M : Module d} {g : Func d} {ts : List d.Ty}
    {args : HVector toType ts} (hsig : ts = g.params.map (·.2)) {S : Memories Mem unit} {N : Nat}
    {x : Ev (Except Stuck (Result (List (DVal d) × Memories Mem unit)))}
    (hx : Ev.NotStuck x) (h : (g.memRunsFrom M (args.cast hsig, S) N) x) :
    ∃ p, g.enter args.toDVals = .ok p ∧ ∃ e, (Func.memCall M N g p.2 p.1 S).run e ∧
      x = e.dropLeft := by
  have hcast : (args.cast hsig).toDVals = args.toDVals := HVector.toDVals_cast _ _
  obtain ⟨p, hp, e, he, hxe⟩ := (Func.memRunsFrom_run hx).1 h
  exact ⟨p, hcast ▸ hp, e, he, hxe⟩

/-- A return or UB of a black box's target in its frame, called on
arguments that refine the source's from memories that refine the source's,
is allowed by the source's callee in its frame, which starts. -/
theorem MemBlackBox.allowed {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : MemBlackBox (Mem := Mem) (unit := unit) M M' bound g g') {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {S S' : Memories Mem unit} (hS : S ⊑ S') {n : Nat} {p' : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p')
    {e' : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (he' : (Func.memCall M' n g' p'.2 p'.1 S').run e')
    (hne : Ev.NotStuck e') (hexh : e' ≠ .ok (.ok .fuelExhausted)) :
    ∃ p, g.enter args.toDVals = .ok p ∧
      MemAllowed (fun N => Func.memCall M N g p.2 p.1 S) e' := by
  have hsig := bb.sig hen'
  have href := bb.refines _ _ S S' (HVector.forall₂_cast hsig hr) hS
  have inv := fun {N x} => Func.memRunsFrom_run_cast (M := M) (args := args) (S := S) (N := N) (x := x) hsig
  match e', he', bb.target_run hen' hne he' with
  | .ok (.ok (.ret (vs', k'))), _, hrun =>
    obtain ⟨s₀, hs₀, hle⟩ := href (.ret vs') ⟨n, hrun⟩
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ =>
      obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ub r) (fun _ h => nomatch h) hN
      match e, he, hx with
      | .ub _, he, rfl => exact ⟨p, hp, .inl ⟨N, r, he⟩⟩
    | .ret vs, ⟨N, hN⟩, hle =>
      obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ok (.ok (.ret vs))) (fun _ h => nomatch h) hN
      match e, he, hx with
      | .ok (.ok (.ret (_, k))), he, rfl => exact ⟨p, hp, .inr ⟨N, vs, k, he, hle⟩⟩
    | .fuelExhausted, _, hle => exact hle.elim
  | .ub r', _, hrun =>
    obtain ⟨s₀, hs₀, hle⟩ := href (.ub r') ⟨n, hrun⟩
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ =>
      obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ub r) (fun _ h => nomatch h) hN
      match e, he, hx with
      | .ub _, he, rfl => exact ⟨p, hp, ⟨N, r, he⟩⟩
    | .ret _, _, hle | .fuelExhausted, _, hle => exact hle.elim
  | .ok (.ok .fuelExhausted), _, _ => exact absurd rfl hexh
  | .ok (.error st), _, _ => exact absurd rfl (hne st)

end Fir
