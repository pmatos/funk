import Fir.Execution.RunPaths
import Fir.Execution.EnvRefine

/-!
# Two modules, compared call by call

The two refinement theorems for whole functions compare the runs of a
function in a source module with its runs in a target module: in the
same module, on arguments that refine others; and in a module where one
callee has a new body. Their proofs share one engine. It follows a path
of the target's run, and finds a way that the source's run _allows_ it:
the source hits UB at some budget, which allows anything, or, for a
return, returns at some budget values that the target's refine.

Each op runs alike in both, on operands of which the target's refine the
source's: what it does on them is allowed by what it does on the
source's, since every op that runs by its own rule is monotone. A call is
where the two modules may differ. Each symbol names, in both, the same
function, whose run the engine follows in turn, or a _black box_: a
function of the source and a function of the target, of the same
parameter types, such that

* on arguments that refine others, the observable behaviour of the
  target's function refines that of the source's: a fact about their
  whole runs, which the engine does not look inside;
* on each argument vector, the target's function diverges, or never runs
  out of fuel at any budget of at least a fixed bound.

Behaviours say nothing of steps. A black box's target may return after a
thousand steps where its source returns after one, or the other way
round. So the engine cannot follow the target at the source's budget, as
it could if every call named the same function. It compares budgets in
two ways, each by induction on the target's budget, in the next two
sections:

* a return or UB of the target is allowed by the source at some budget.
  A caller's budget is its callee's budget plus that of the rest of the
  caller's ops after the call: with more fuel, a run does the same thing
  and leaves more steps;
* running out of fuel needs the black box's bound.

A black-box call that the target runs is allowed by the source's call:
the target's callee starts on arguments of its parameter types, so the
source's are of the source callee's, and the source's callee ends in a
way that the black box allows.
-/

namespace Fir

open SetM

/-- A vector of values, seen at a list of types equal to its own. -/
def HVector.cast {α : Type} {f : α → Type} {as bs : List α} (h : as = bs) (v : HVector f as) :
    HVector f bs := h ▸ v

/-- Seen at other types, a vector holds the same values. -/
theorem HVector.toDVals_cast {Ty : Type} [TyDenote Ty] {ts ts' : List Ty} (h : ts = ts')
    (v : HVector toType ts) : (v.cast h).toDVals = v.toDVals := by
  subst h; rfl

/-- Seen at other types, two vectors are related as they were. -/
theorem HVector.forall₂_cast {α : Type} {f : α → Type} {r : {a : α} → f a → f a → Prop}
    {as bs : List α} (h : as = bs) {v w : HVector f as} (hr : v.Forall₂ r w) :
    (v.cast h).Forall₂ r (w.cast h) := by
  subst h; exact hr

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM] [TyRefinement d.Ty]

/-- The run hits UB at some budget. -/
def SomeUB {α : Type} (src : Nat → ExceptT Stuck SetM α) : Prop :=
  ∃ N r, (src N).run (.ub r)

/-- The source `src`, a run at each budget, allows the target's path: it
hits UB at some budget, which allows anything, or, for a return, it
returns at some budget values that the target's refine. A path that runs
out of fuel or is stuck asks nothing here. -/
def Allowed (src : Nat → ExceptT Stuck SetM (Result (List (DVal d) × Nat))) :
    Ev (Except Stuck (Result (List (DVal d) × Nat))) → Prop
  | .ok (.ok (.ret (vs', _))) =>
    SomeUB src ∨ ∃ N vs k, (src N).run (.ok (.ok (.ret (vs, k)))) ∧ vs ⊑ vs'
  | .ub _ => SomeUB src
  | _ => True

/-- A black box: the function `g` of the source module `M`, whose calls
the target module `M'` runs as calls of `g'`. Their parameters have the
same types; on arguments that refine others, the behaviour of `g'`
refines that of `g`; and on each argument vector, `g'` diverges, or none
of its runs with `bound` steps or more runs out of fuel. -/
structure BlackBox (M M' : Module d) (bound : Nat) (g g' : Func d) : Prop where
  params : g'.params.map (·.2) = g.params.map (·.2)
  refines : ∀ a a' : HVector toType (g.params.map (·.2)), a.Forall₂ TyRefinement.IsRefinedBy a' →
    observable (g.runs M a) ⊑ observable (g'.runs M' (a'.cast params.symm))
  bounded : ∀ a' : HVector toType (g'.params.map (·.2)),
    (∀ m, (g'.runs M' a' m).outcomes .fuelExhausted) ∨
      ∀ m, bound ≤ m → ¬ (g'.runs M' a' m).outcomes .fuelExhausted

/-- The target module `M'` runs each call as the source `M` does: each
symbol names the same function in both, or a black box. -/
def CallsRefined (M M' : Module d) (bound : Nat) : Prop :=
  ∀ s, M'.func? s = M.func? s ∨
    ∃ g g', M.func? s = some g ∧ M'.func? s = some g' ∧ BlackBox M M' bound g g'

/-- The way a path ends, with `k` more steps left if it returns. -/
def Ev.addLeft (k : Nat) :
    Ev (Except Stuck (Result (α × Nat))) → Ev (Except Stuck (Result (α × Nat)))
  | .ok (.ok (.ret (a, i))) => .ok (.ok (.ret (a, i + k)))
  | e => e

omit [TyRefinement d.Ty] in
/-- A caller whose callee returns at the budget `N₁`, and whose rest ends
so at the budget `N₂`, ends so at `N₁ + N₂ + 1`, leaving the callee's
steps too. -/
theorem Func.call_cont {M : Module d} {f g : Func d} {env genv : Env d} {o : Operation d}
    {os body : List (Operation d)} {args : HVector toType (sig o.op)} {s : Name}
    {vs : List (DVal d)} {k N₁ N₂ : Nat} {x : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (hreg : o.regions = []) (hargs : env.operands (sig o.op) o.operands = .ok args)
    (hT : isTerminator o.op = false) (hc : callee? o.op = some s) (hg : M.func? s = some g)
    (hen : g.enter args.toDVals = .ok (body, genv))
    (hx : (Func.runOps (m := SetM) M N₁ g genv body).run (.ok (.ok (.ret (vs, k)))))
    (hty : vs.map (·.1) = returnTypes o.op) (hlen : (o.results.map (·.1)).length = vs.length)
    (hne : Ev.NotStuck x) (hxe : x ≠ .ok (.ok .fuelExhausted))
    (hcont : (Func.runOps (m := SetM) M N₂ f ((o.results.map (·.1)).zip vs ++ env) os).run x) :
    (Func.runOps (m := SetM) M (N₁ + N₂ + 1) f env (o :: os)).run (x.addLeft k) := by
  have hk := Func.runOps_left_le M N₁ g genv body vs k hx
  have hne' : Ev.NotStuck (x.addLeft k) := by
    intro st h
    match x, h with
    | .ok (.error _), _ => exact hne _ rfl
  refine (Func.stepPath_iff hne').2 (.callRet hreg hargs hT hc hg hen
    ((Func.runOps_ahead M N₁ N₂ g genv body).up_ret _ _ hx) hty hlen ?_)
  rw [Nat.min_eq_left (Nat.add_le_add_right hk _), Nat.add_comm k]
  have ha := Func.runOps_ahead M N₂ k f ((o.results.map (·.1)).zip vs ++ env) os
  match x, hcont with
  | .ok (.ok (.ret (a, i))), h => exact ha.up_ret _ _ h
  | .ub r, h => exact ha.up_ub _ h
  | .ok (.ok .fuelExhausted), _ => exact absurd rfl hxe
  | .ok (.error st), _ => exact absurd rfl (hne st)

omit [TyRefinement d.Ty] in
/-- A path of a run of a function that is not stuck is a path of the run
of its entry block's ops, from where it starts. -/
theorem Func.run_inv {M : Module d} {f : Func d} {a : HVector toType (f.params.map (·.2))}
    {n : Nat} {x : Ev (Except Stuck (Result (List (DVal d))))} (hne : Ev.NotStuck x)
    (h : (f.run M (m := SetM) a n).run x) :
    ∃ p, f.enter a.toDVals = .ok p ∧ ∃ e, (Func.runOps (m := SetM) M n f p.2 p.1).run e ∧
      x = e.dropLeft := by
  rcases (Func.run_run M f a n x).1 h with ⟨p, hp, e, he, rfl⟩ | ⟨st, _, rfl⟩
  · exact ⟨p, hp, e, he, rfl⟩
  · exact absurd rfl (hne st)

omit [TyRefinement d.Ty] in
/-- A return of a function at some budget is a return of the run of its
entry block's ops, which starts. -/
theorem Func.runs_ret_inv {M : Module d} {g : Func d} {a : HVector toType (g.params.map (·.2))}
    {N : Nat} {vs : List (DVal d)} (h : (g.runs M a N).outcomes (.ret vs)) :
    ∃ p, g.enter a.toDVals = .ok p ∧
      ∃ k, (Func.runOps (m := SetM) M N g p.2 p.1).run (.ok (.ok (.ret (vs, k)))) := by
  obtain ⟨p, hp, e, he, hx⟩ := Func.run_inv (x := .ok (.ok (.ret vs))) (fun _ h => nomatch h) h
  match e, he, hx with
  | .ok (.ok (.ret (_, k))), he, hx => cases hx; exact ⟨p, hp, k, he⟩
  | .ok (.ok .fuelExhausted), _, hx | .ok (.error _), _, hx | .ub _, _, hx => cases hx

omit [TyRefinement d.Ty] in
/-- UB of a function at some budget is UB of the run of its entry block's
ops, which starts. -/
theorem Func.runs_ub_inv {M : Module d} {g : Func d} {a : HVector toType (g.params.map (·.2))}
    {N : Nat} {r : String} (h : (g.runs M a N).outcomes (.ub r)) :
    ∃ p, g.enter a.toDVals = .ok p ∧ (Func.runOps (m := SetM) M N g p.2 p.1).run (.ub r) := by
  obtain ⟨p, hp, e, he, hx⟩ := Func.run_inv (x := .ub r) (fun _ h => nomatch h) h
  match e, he, hx with
  | .ub _, he, hx => cases hx; exact ⟨p, hp, he⟩
  | .ok (.ok (.ret _)), _, hx | .ok (.ok .fuelExhausted), _, hx | .ok (.error _), _, hx => cases hx

omit [TyRefinement d.Ty] in
/-- Running out of fuel, for a function at some budget, is running out of
fuel in the run of its entry block's ops, which starts. -/
theorem Func.runs_exh_inv {M : Module d} {g : Func d} {a : HVector toType (g.params.map (·.2))}
    {N : Nat} (h : (g.runs M a N).outcomes .fuelExhausted) :
    ∃ p, g.enter a.toDVals = .ok p ∧
      (Func.runOps (m := SetM) M N g p.2 p.1).run (.ok (.ok .fuelExhausted)) := by
  obtain ⟨p, hp, e, he, hx⟩ := Func.run_inv (x := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h) h
  match e, he, hx with
  | .ok (.ok .fuelExhausted), he, _ => exact ⟨p, hp, he⟩
  | .ok (.ok (.ret _)), _, hx | .ub _, _, hx | .ok (.error _), _, hx => cases hx

omit [TyRefinement d.Ty] in
/-- A path of the run of a function's entry block's ops, from where it
starts, is a path of the function's run. -/
theorem Func.runs_of_runOps {M : Module d} {g : Func d} {a : HVector toType (g.params.map (·.2))}
    {N : Nat} {p : List (Operation d) × Env d} (hp : g.enter a.toDVals = .ok p)
    {e : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (he : (Func.runOps (m := SetM) M N g p.2 p.1).run e) : (g.runs M a N) e.dropLeft :=
  (Func.run_run M g a N _).2 (.inl ⟨p, hp, e, he, rfl⟩)

/-- A call that enters a black box's target passes arguments of the
parameter types of the black box's source. -/
theorem BlackBox.sig {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : BlackBox M M' bound g g') {ts : List d.Ty} {args' : HVector toType ts}
    {p : List (Operation d) × Env d} (hen' : g'.enter args'.toDVals = .ok p) :
    ts = g.params.map (·.2) := by
  obtain ⟨_, _, _, hty', _⟩ := Func.enter_eq_ok hen'
  rw [HVector.toDVals_types] at hty'
  exact hty'.trans bb.params

/-- A return or UB of a black box's target, called on arguments that
refine the source's, is allowed by the source's callee, which starts. -/
theorem BlackBox.allowed {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : BlackBox M M' bound g g') {ts : List d.Ty} {args args' : HVector toType ts}
    (hr : args.Forall₂ TyRefinement.IsRefinedBy args') {n : Nat} {p' : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p')
    {e' : Ev (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : (Func.runOps (m := SetM) M' n g' p'.2 p'.1).run e')
    (hne : Ev.NotStuck e') (hexh : e' ≠ .ok (.ok .fuelExhausted)) :
    ∃ p, g.enter args.toDVals = .ok p ∧
      Allowed (fun N => Func.runOps (m := SetM) M N g p.2 p.1) e' := by
  have hsig := bb.sig hen'
  have hen'' : g'.enter ((args'.cast hsig).cast bb.params.symm).toDVals = .ok p' := by
    rw [HVector.toDVals_cast, HVector.toDVals_cast]; exact hen'
  have hrun := Func.runs_of_runOps hen'' he'
  have href := bb.refines _ _ (HVector.forall₂_cast hsig hr)
  have hcast : (args.cast hsig).toDVals = args.toDVals := HVector.toDVals_cast _ _
  match e', he', hrun with
  | .ok (.ok (.ret (vs', k'))), he', hrun =>
    obtain ⟨s₀, hs₀, hle⟩ := href (.ret vs') ⟨n, hrun⟩
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ =>
      obtain ⟨p, hp, hx⟩ := Func.runs_ub_inv hN
      exact ⟨p, hcast ▸ hp, .inl ⟨N, r, hx⟩⟩
    | .ret vs, ⟨N, hN⟩, hle =>
      obtain ⟨p, hp, k, hx⟩ := Func.runs_ret_inv hN
      exact ⟨p, hcast ▸ hp, .inr ⟨N, vs, k, hx, hle⟩⟩
    | .fuelExhausted, _, hle => exact hle.elim
  | .ub r', he', hrun =>
    obtain ⟨s₀, hs₀, hle⟩ := href (.ub r') ⟨n, hrun⟩
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ =>
      obtain ⟨p, hp, hx⟩ := Func.runs_ub_inv hN
      exact ⟨p, hcast ▸ hp, ⟨N, r, hx⟩⟩
    | .ret _, _, hle | .fuelExhausted, _, hle => exact hle.elim
  | .ok (.ok .fuelExhausted), _, _ => exact absurd rfl hexh
  | .ok (.error st), _, _ => exact absurd rfl (hne st)

end Fir
