import Fir.Execution.Calls
import Fir.Execution.Replace

/-!
# Valid modules run on valid op instances

The lawful class, which holds the poison obligations of a dialect, speaks
only of op instances whose types validation accepts
(ADR-2026-10-29-2006), and its totality and monotonicity only of those
that run by their own rule: a terminator, or an op with no callee
(ADR-2026-10-29-2006). That is enough for every valid module, because a
valid module holds no other instance:

* every op of a valid function is a valid op instance. Validation checks
  each operand's type against the type of the value it names, and each
  result's type is the type of a value that the function defines, and
  every type that a valid function states is valid;
* so a dialect whose terminators and ops with no callee are monotone at
  every valid op instance gives monotone ops to every valid function. The
  general refinement theorems follow the target's run into its callees,
  and ask monotonicity only of the ops that the run can reach: the ops of
  the function that runs and of the source module's functions
  (`docs/decisions/semantics-refinement.md#the-ops-a-run-reaches`);
* the class gives the totality that progress with calls asks of every
  terminator and every op with no callee of the module. A function of a
  module whose functions are all valid and run within the module has an
  outcome at every budget, on every argument vector, calls and recursion
  included. No path of such a function's run is stuck either, whatever
  its ops do, as the section on progress with calls proves;
* a lawful dialect gets both function-level refinement theorems for
  every function of a valid module by the class alone: on arguments that
  refine others, and on replacing a callee's body, whatever the new body.

The core dialect meets the general theorems' hypothesis with its ops' own
obligations, which hold at every width, so refinement holds for every
core module, valid or not (the section on refinement through core calls).
-/

namespace Fir

variable {d : Dialect} [DialectSignature d] [DialectValidation d]

/-- Every op of a valid function is a valid op instance: validation accepts
each of its operand types and each of its result types. -/
theorem Func.Valid.typesValid {ctx : ModuleContext d} {f : Func d} (hv : f.Valid ctx)
    {b : Block d} (hb : b ∈ f.blocks) {o : Operation d} (ho : o ∈ b.body) : TypesValid o.op := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  obtain ⟨-, hops, hres, -⟩ := hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)
  have hdef : ∀ p ∈ f.defs, validTy p.2 := fun p hp =>
    hv.types p.2 (List.mem_append_right _ (List.mem_map_of_mem hp))
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have hs : some t ∈ b.body[i].operands.map f.typeOf := hops ▸ List.mem_map_of_mem ht
    obtain ⟨x, -, hx⟩ := List.mem_map.1 hs
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact hdef p (List.mem_of_find?_eq_some hp)
  · rw [← hres] at ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    exact hdef p (Func.mem_defs_result hb ho hp)

section

variable [TyDenote d.Ty] [TyRefinement d.Ty] [DialectCall d] [DialectDenote d SetM]

/-- Every terminator and every op with no callee of a valid function is
monotone, when every such op is at every valid op instance. -/
theorem Func.Valid.opsMonotone
    (hmono : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
      OpMonotone op)
    {ctx : ModuleContext d} {f : Func d} (hv : f.Valid ctx) : f.OpsMonotone :=
  fun _ hb o ho => hmono o.op (hv.typesValid hb ho)

end

variable [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty] [DialectEffects d]
  [DialectCall d] [DialectDenote d SetM] [LawfulDialectPoison d] {ctx : ModuleContext d}
  {M : Module d}

/-- A run of a function of the module `M` has an outcome at every budget,
on any argument vector, calls and recursion included, when the dialect is
lawful and every function of `M` is valid and runs within `M`. -/
theorem Func.progress_of_lawful (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    (hm : ∀ g ∈ M.funcs, g.InModule M) {f : Func d} (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.runs M args) :=
  Func.progress_of_inModule hv hm
    (fun g hg _ hb o ho hc => LawfulDialectPoison.total o.op ((hv g hg).typesValid hb ho) hc)
    hf args

open SetM in
/-- Refined arguments, by the lawful class alone: a function's behaviour
on arguments that refine others, a poison by any value, refines its
behaviour on those others, for every function of a module whose functions
are all valid, calls and recursion included. -/
theorem Func.runs_args_isRefinedBy_of_lawful (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func d}
    (hf : f ∈ M.funcs) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.runs M a) ⊑ observable (f.runs M a') :=
  Func.runs_args_isRefinedBy M (fun g hg => (hv g hg).opsMonotone LawfulDialectPoison.monotone) f
    ((hv f hf).opsMonotone LawfulDialectPoison.monotone) ha

/-- Congruence in the callee, by the lawful class alone: in a valid
module, replacing the body of its function `@g` with one under which
`@g`, run in the new module, refines `@g` in the old, refines every
function of the module, calls and recursion included, whatever the new
body. It asks that the refinement of values be reflexive and transitive,
and that `@g` have finitely many argument vectors. -/
theorem Func.runs_replaceBody_isRefinedBy_of_lawful
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hfin : ∃ L : List (HVector toType (g.params.map (·.2))), ∀ a, a ∈ L)
    (h : g.runs M ⊑ (g.replaceBody g.name b).runs (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.runs M ⊑ (f.replaceBody g.name b).runs (M.replaceBody g.name b) :=
  Func.runs_replaceBody_isRefinedBy
    (fun g hg => (hM.funcs g hg).opsMonotone LawfulDialectPoison.monotone) hrefl htrans
    hM.symbolsUnique hg b hfin h hf

end Fir
