import Fir.Execution.Jumps

/-!
# The steps of a call

A call is the one step of a run that the section on progress with jumps
and loops does not take. The section after this one proves that it is never
stuck and always has a way to go on, for a call in a valid function whose
module names its callee. It rests on these facts:

* _A sequence has a path when its parts have one._ A path of a callee's
  run that ends with UB or stuck ends its caller's run so, so a caller's
  run has a path whenever its callee's has one and the caller has one
  after each return of the callee.
* _The callee is found._ When the module's symbol table gives a symbol a
  type, the module has a function of that symbol and that type, which the
  run finds by the same search, and it is a function of the module.
* _A function returns values of its result types._ The interpreter checks
  the types of the values that a function returns before it returns them,
  so every return of a run of a function's ops returns values of the
  function's result types, whatever its ops do. A call whose types are its
  callee's then receives values of its own result types.
* _The callee starts._ A run of a function on values of its parameter
  types starts at its entry block, with its parameters bound to them, when
  its entry block declares no arguments.
* _At the start of a function, binding its parameters holds every value in
  scope._ Only the parameters are in scope at the entry block's first op,
  so the run's environment holds every value in scope there.
* _An op's results join the scope._ After an op binds its results to
  values of their types, the environment holds every value in scope at the
  next op, as the section on scope along a run proves of an op that is not
  a call.
-/

namespace Fir

open SetM

/-- `x >>= g` has a path when `x` has one, and `g` has one on each result
of `x`. -/
theorem HasPath.bind {α β : Type} {x : ExceptT Stuck SetM α} {g : α → ExceptT Stuck SetM β}
    (hx : HasPath x) (hg : ∀ a, x.run (.ok (.ok a)) → HasPath (g a)) : HasPath (x >>= g) := by
  obtain ⟨e, he⟩ := hx
  match e, he with
  | .ok (.ok a), he => exact HasPath.bind_ok he (hg a he)
  | .ok (.error st), he => exact ⟨_, (run_bind x g _).2 (.inr (.inl ⟨st, he, rfl⟩))⟩
  | .ub r, he => exact ⟨_, (run_bind x g _).2 (.inr (.inr ⟨r, he, rfl⟩))⟩

section

variable {d : Dialect}

/-- The module's symbol table gives a symbol a type only when the module
has a function of that symbol and that type, which the run finds. -/
theorem Module.func?_of_symbols {M : Module d} {s : Name} {ft : FuncType d}
    (h : M.symbols s = some ft) :
    ∃ g, M.func? s = some g ∧ g ∈ M.funcs ∧ g.params.map (·.2) = ft.params ∧
      g.results = ft.results := by
  obtain ⟨g, hg, hty⟩ := Option.map_eq_some_iff.1 h
  subst hty
  exact ⟨g, hg, List.mem_of_find?_eq_some hg, rfl, rfl⟩

variable [TyDenote d.Ty]

/-- Every return of `s` returns values of the types `ts`. -/
def ReturnsTypes (ts : List d.Ty) (s : ExceptT Stuck SetM (Result (List (DVal d) × Nat))) :
    Prop :=
  ∀ vs k, s.run (.ok (.ok (.ret (vs, k)))) → vs.map (·.1) = ts

namespace ReturnsTypes

variable {ts : List d.Ty}

/-- `x >>= g` returns values of the types `ts` when `g` does on each
result of `x`. -/
theorem bind {β : Type} {x : ExceptT Stuck SetM β}
    {g : β → ExceptT Stuck SetM (Result (List (DVal d) × Nat))}
    (h : ∀ b, x.run (.ok (.ok b)) → ReturnsTypes ts (g b)) : ReturnsTypes ts (x >>= g) := by
  intro vs k hk
  rcases (run_bind x g _).1 hk with ⟨b, hb, hg⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
  · exact h b hb vs k hg
  · cases he
  · cases he

/-- A stuck computation returns nothing. -/
theorem of_stuck {r : String} :
    ReturnsTypes ts (liftExcept (stuck r) : ExceptT Stuck SetM (Result (List (DVal d) × Nat))) :=
  fun _ _ hk => nomatch (run_liftExcept _ _).1 hk

/-- A run that runs out of fuel returns nothing. -/
theorem exhausted :
    ReturnsTypes ts (pure .fuelExhausted : ExceptT Stuck SetM (Result (List (DVal d) × Nat))) :=
  fun _ _ hk => nomatch (run_pure _ _).1 hk

/-- A return of values of the types `ts`. -/
theorem ret {vs : List (DVal d)} {k : Nat} (h : vs.map (·.1) = ts) :
    ReturnsTypes ts (pure (.ret (vs, k)) : ExceptT Stuck SetM (Result (List (DVal d) × Nat))) :=
  fun _ _ hk => by cases (run_pure _ _).1 hk; exact h

end ReturnsTypes

variable [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectDenote d SetM]

/-- A run of ops of `f` returns values of `f`'s result types: the
interpreter checks them before it returns. -/
theorem Func.runOps_returns (M : Module d) (n : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)),
      ReturnsTypes f.results (Func.runOps (m := SetM) M n f env os) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env os
    match n, os with
    | 0, _ => simp only [Func.runOps]; exact ReturnsTypes.exhausted
    | _ + 1, [] => simp only [Func.runOps]; exact ReturnsTypes.of_stuck
    | k + 1, o :: os =>
      simp only [Func.runOps]
      all_goals repeat' (first
        | (apply ReturnsTypes.bind; intro _ _)
        | split
        | exact ReturnsTypes.of_stuck
        | exact ReturnsTypes.exhausted
        | exact ReturnsTypes.ret (by rw [HVector.toDVals_types]; assumption)
        | exact ih _ (Nat.lt_succ_self _) _ _ _
        | exact ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _)

omit [DialectSignature d] [DialectCall d] [DialectDenote d SetM] in
/-- A run of `f` starts at its entry block, with its parameters bound to
values of their types, when its entry block declares no arguments. -/
theorem Func.enter_ok {f : Func d} {e : Block d} (he : f.blocks.head? = some e)
    (hep : e.params = []) {dvs : List (DVal d)} (h : dvs.map (·.1) = f.params.map (·.2)) :
    f.enter dvs = .ok (e.body, (f.params.map (·.1)).zip dvs) := by
  simp [Func.enter, he, hep, h]
  rfl

variable [DialectValidation d] {ctx : ModuleContext d} {f : Func d} {b : Block d}

omit [DecidableEq d.Ty] [DialectCall d] [DialectDenote d SetM] in
/-- The parameters of a valid function, bound to values of their types,
are all that is in scope at its entry block's first op. -/
theorem Env.scoped_entry (hv : f.Valid ctx) {e : Block d} (he : f.blocks.head? = some e)
    (hep : e.params = []) {dvs : List (DVal d)} (h : dvs.map (·.1) = f.params.map (·.2)) :
    Env.Scoped ((f.params.map (·.1)).zip dvs) f e.label 0 := by
  have hs := Env.scoped_bind (env := []) (f := f) (l := e.label) (i := 0) (ps := f.params) h
    (fun p hp => Func.typeOf_of_mem hv.namesUnique (List.mem_append_left _ hp))
    (fun x hx hnot => absurd (Func.mem_params_of_inScope hv he hep hx) hnot)
  simpa using hs

omit [DecidableEq d.Ty] [DialectCall d] [DialectDenote d SetM] in
/-- After the op at index `i` of a block binds its results to values of
their types, the environment holds every value in scope at the next op. -/
theorem Func.scoped_results (hv : f.Valid ctx) (hb : b ∈ f.blocks) {i : Nat}
    (hi : i < b.body.length) {env : Env d} (hold : env.Scoped f b.label i)
    {vs : List (DVal d)} (hty : vs.map (·.1) = b.body[i].results.map (·.2)) :
    Env.Scoped ((b.body[i].results.map (·.1)).zip vs ++ env) f b.label (i + 1) :=
  Env.scoped_bind hty
    (fun _ hp => Func.typeOf_of_mem hv.namesUnique
      (Func.mem_defs_result hb (List.getElem_mem hi) hp))
    (fun x hx hnot => hold x (Func.inScope_of_next hv hb hi hx hnot))

end

end Fir
