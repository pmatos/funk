import Fir.Execution.RefineDown

/-!
# A call on arguments that refine others

The first of the two refinement theorems for whole functions: on
arguments that refine others, such as a poison replaced by any value of
its type, a function's observable behaviour refines its behaviour on
those others. It holds for every function of every module, calls and
recursion included, when the terminators and the ops with no callee of
the function and of the module's functions are monotone. The section on refinement through core
calls states it for the core dialect, and the section on what the lawful
class gives for every function of a valid module of a lawful dialect, by
the class alone. A call passes its arguments to its callee, so a call on
arguments that refine others refines the call on those others. This is
the counterpart, for a whole function, of monotonicity, which speaks only
of ops that run by their own rule: an op with a callee has no rule of its
own (ADR-2026-11-02-1514).

Both function-level theorems are instances of one. Take a function of a
source module, and the same function of a target module whose calls name
the same functions as the source's, or black boxes. On arguments that
refine others, its behaviour in the target refines its behaviour in the
source. Refined arguments are the case where the target is the source:
every call names the same function, and there is no black box.

Each outcome of the target is allowed by one of the source:

* A return or UB at some budget: the source's run hits UB at some budget,
  or returns at some budget values that the target's refine (the section
  on returns and UB).
* Divergence, when the target runs out of fuel at every budget. If the
  source hits UB at some budget, it allows anything. If not, then for
  each budget of the source, the target runs out of fuel at a large
  enough budget, on a path that the source allows at its budget (the
  section on running out of fuel): the source runs out of fuel there. So
  the source diverges.

The theorem asks nothing of validity: it compares outcomes, and a stuck
path is none. It means most for valid modules, whose runs have no stuck
path and an outcome at every budget (the section on core functions with
calls), so that neither behaviour is empty or misses a path.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM] [TyRefinement d.Ty]

/-- A function's behaviour in the target module, on arguments that refine
others, refines its behaviour in the source module on those others, when
every call names the same function in both modules or a black box, and
every terminator and every op with no callee of the function and of the
source module's functions is monotone. -/
theorem Func.runs_isRefinedBy_of_calls {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.OpsMonotone) {bound : Nat} (hcalls : CallsRefined M M' bound)
    (f : Func d) (hf : f.OpsMonotone) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.runs M a) ⊑ observable (f.runs M' a') := by
  have start : ∀ {p' : List (Operation d) × Env d}, f.enter a'.toDVals = .ok p' →
      ∃ genv, f.enter a.toDVals = .ok (p'.1, genv) ∧ genv.IsRefinedBy p'.2 :=
    fun hen' => Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy ha) hen'
  intro t ht
  match t, ht with
  | .ret vs', ⟨n, hn⟩ =>
    obtain ⟨p', hen', k', hx⟩ := Func.runs_ret_inv hn
    obtain ⟨genv, hen, henv⟩ := start hen'
    rcases Func.runOps_allowed hmono hcalls n f genv p'.2 p'.1 hf (hf.enter hen') henv _ hx with
      ⟨N, r, h⟩ | ⟨N, vs, k, h, hvs⟩
    · exact ⟨.ub r, ⟨N, Func.runs_of_runOps hen h⟩, trivial⟩
    · exact ⟨.ret vs, ⟨N, Func.runs_of_runOps hen h⟩, hvs⟩
  | .ub r', ⟨n, hn⟩ =>
    obtain ⟨p', hen', hx⟩ := Func.runs_ub_inv hn
    obtain ⟨genv, hen, henv⟩ := start hen'
    obtain ⟨N, r, h⟩ := Func.runOps_allowed hmono hcalls n f genv p'.2 p'.1 hf (hf.enter hen')
      henv _ hx
    exact ⟨.ub r, ⟨N, Func.runs_of_runOps hen h⟩, trivial⟩
  | .fuelExhausted, ht =>
    classical
    by_cases hU : ∃ N r, (f.runs M a N).outcomes (.ub r)
    · obtain ⟨N, r, h⟩ := hU
      exact ⟨.ub r, ⟨N, h⟩, trivial⟩
    refine ⟨.fuelExhausted, fun N => ?_, trivial⟩
    obtain ⟨p', hen', hx⟩ := Func.runs_exh_inv (ht ((bound + 1) * (N + 1)))
    obtain ⟨genv, hen, henv⟩ := start hen'
    rcases Func.runOps_allowedBelow hmono hcalls _ f genv p'.2 p'.1 N hf (hf.enter hen') henv
      (Nat.le_refl _) _ hx with h | ⟨N', r, h⟩
    · exact Func.runs_of_runOps hen h
    · exact absurd ⟨N', r, Func.runs_of_runOps hen h⟩ hU

/-- Refined arguments: a function's behaviour on arguments that refine
others, a poison by any value, refines its behaviour on those others, in
every module, calls and recursion included, when every terminator and
every op with no callee of the function and of the module's functions is
monotone. -/
theorem Func.runs_args_isRefinedBy (M : Module d) (hmono : ∀ g ∈ M.funcs, g.OpsMonotone)
    (f : Func d) (hf : f.OpsMonotone) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.runs M a) ⊑ observable (f.runs M a') :=
  Func.runs_isRefinedBy_of_calls hmono (bound := 0) (fun _ => .inl rfl) f hf ha

end Fir
