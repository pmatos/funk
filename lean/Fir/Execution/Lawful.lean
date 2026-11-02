import Fir.Execution.Calls

/-!
# Valid modules run on valid op instances

The lawful class `LawfulDialectPoison` speaks only of op instances whose
types validation accepts (`TypesValid`, ADR-2026-11-02-1515), and its
totality and monotonicity only of those that run by their own rule: a
terminator, or an op with no callee (ADR-2026-11-02-1514). That is enough
for every valid module, because a valid module holds no other instance:

* every op of a valid function is a valid op instance
  (`Func.Valid.typesValid`). Validation checks each operand's type
  against the type of the value it names, and each result's type is the
  type of a value that the function defines, and every type that a valid
  function states is valid;
* so the class gives the totality that progress with calls asks of every
  terminator and every op with no callee of the module
  (`Module.calls_hasPath`). A function of a module whose functions are all
  valid and run within the module has an outcome at every budget, on every
  argument vector, calls and recursion included (`Func.progress_of_lawful`);
* no path of such a function's run is stuck, whatever its ops do
  (`Func.neverStuck_of_inModule`): that needs no property of the ops.

Refinement asks more than the class gives. The general theorems of the
sections on refined arguments and on congruence in the callee follow the
target's run into its callees, and ask that every terminator and every op
with no callee be monotone at every op instance, not only at those of the
modules they compare. The class covers only valid instances, so it does
not give that by itself. The core dialect meets it with its ops' own
obligations, which hold at every width (`Core.Op.monotone_all`), so
refinement holds for every core module (the section on refinement through
core calls).
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

variable [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty] [DialectPoison d]
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

end Fir
