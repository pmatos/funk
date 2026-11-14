import Fir.Execution.MemoryRefineRuns

/-!
# Congruence in the callee, with memory

The second of the two refinement theorems for whole functions with memory:
replacing a callee's body refines every caller when the callee, run in the
new module, refines the old one, recursion included. What replacing a
callee means is as for runs in the set monad (the section on congruence in
the callee).

A callee runs from the memories its caller reached, and its caller goes on
from the memories it leaves. So the hypothesis compares the new function in
the new module with `@g` in the old _from every memories_, the memories they
end with included, as their runs from given memories: refinement of runs
with memory alone, from the empty memories, says nothing of a call made
from other memories. The conclusion holds of every function of the module
in the same sense, and so of its runs with memory.

The proof is the one for runs in the set monad. Every call of `@g` is a
black box with memory (`Module.replaceBody_memCallsRefined`), whose source is `@g` in the old module and whose
target is the new function in the new module, and every other symbol names
the same function in both modules. The black box refines: from memories
that refine others, on arguments that refine others, `@g` is refined by
`@g` from the refined ones (the section on a call with memory on arguments
and memories that refine others), which is refined by the new function, by
the hypothesis.

The theorem asks for a bound: on each argument vector and from each
memories, the new function diverges, or from some budget on never runs out
of fuel. For runs in the set monad, finitely many argument vectors give one
budget for all
(`docs/decisions/semantics-refinement.md#congruence-in-the-callee`). The
memories a call starts from are infinitely many, so no such argument gives a
bound here, and the theorem asks for one budget past which no run of the new
function from any memories runs out of fuel unless it diverges. When every
op of the dialect has finitely many outcomes, no budget is needed (the
section on congruence in the callee with ops of finitely many outcomes), as
for the core. This form asks no finitely many outcomes, so it stays for a
dialect whose ops may have infinitely many.

For a dialect lawful in its monotonicity, every function of a valid module
refines itself on refined arguments and memories by the class alone, at
every naming of its memories. Congruence in the callee then asks only what
the class cannot give: that refinement of values be reflexive and
transitive, the budget for the new function, and that it refine the old
one from every memories.
-/

namespace Fir

open SetM Memory

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-- In a module whose symbols are unique, the module with `@g`'s new body
runs each call as the module does, when `@g`, run in the new module from
given memories, refines `@g` in the old: each symbol other than `@g` names
the same function in both, and `@g` is a black box, under the hypotheses of
congruence in the callee but the budget and reflexivity. -/
theorem Module.replaceBody_memCallsRefined {M : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : g.memRunsFrom (Mem := Mem) (unit := unit) M ⊑
      (g.replaceBody g.name b).memRunsFrom (Mem := Mem) (unit := unit) (M.replaceBody g.name b)) :
    MemCallsRefined Mem unit M (M.replaceBody g.name b) := by
  have hobs : ∀ {x y z : List (DVal d) × Memories Mem unit}, x ⊑ y → y ⊑ z → x ⊑ z :=
    fun h₁ h₂ => ⟨List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans) h₁.1 h₂.1,
      Memories.isRefinedBy_trans h₁.2 h₂.2⟩
  have bb : MemBlackBox (Mem := Mem) (unit := unit) M (M.replaceBody g.name b) g
      (g.replaceBody g.name b) :=
    { params := rfl
      refines := fun a a' S S' ha hS => Behaviour.isRefinedBy_trans hobs
        (Func.memRunsFrom_args_isRefinedBy M hmono g (hmono g hg) ha hS) (h (a', S')) }
  intro x
  by_cases hx : x = g.name
  · subst hx
    exact .inr ⟨g, _, Module.func?_of_mem hnd hg, Module.func?_replaceBody_self hnd hg b, bb⟩
  · exact .inl (Module.func?_replaceBody_of_ne hx)

/-- Congruence in the callee, with memory: in a module whose symbols are
unique, replacing the body of its function `@g` with one under which `@g`,
run in the new module from given memories, refines `@g` in the old, refines
every function of the module from given memories, calls and recursion
included. It asks that every terminator and every op with no callee of the
old module's functions be monotone with memory, that the refinement of
values be reflexive and transitive, and for one budget past which no run
of the new `@g` runs out of fuel unless it diverges. -/
theorem Func.memRunsFrom_replaceBody_isRefinedBy {M : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hbound : ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := Mem) (unit := unit)
      (M.replaceBody g.name b)).BoundedBy B)
    (h : g.memRunsFrom (Mem := Mem) (unit := unit) M ⊑
      (g.replaceBody g.name b).memRunsFrom (Mem := Mem) (unit := unit) (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRunsFrom (Mem := Mem) (unit := unit) M ⊑
      (f.replaceBody g.name b).memRunsFrom (Mem := Mem) (unit := unit) (M.replaceBody g.name b) := by
  by_cases hfg : f.name = g.name
  · rw [eq_of_nodup_map hnd hf hg hfg]
    exact h
  show f.memRunsFrom M ⊑ Func.memRunsFrom _ { f with body := if f.name = g.name then b else f.body }
  rw [ite_eq_right hfg]
  obtain ⟨bound, hbound⟩ := hbound
  have hcalls := Module.replaceBody_memCallsRefined (Mem := Mem) (unit := unit) hmono htrans
    hnd hg b h
  have hbnd : MemCallsBounded Mem unit M (M.replaceBody g.name b) bound := fun x g' hx hne => by
    by_cases hxg : x = g.name
    · subst hxg
      rw [Module.func?_replaceBody_self hnd hg b] at hx
      cases hx
      exact hbound
    · exact absurd (Module.func?_replaceBody_of_ne hxg) hne
  exact fun p => Func.memRunsFrom_isRefinedBy_of_calls hmono hcalls hbnd f (hmono f hf)
    (HVector.forall₂_refl (fun v => hrefl v) p.1) (Memories.isRefinedBy_refl p.2)

variable [DialectValidation d]

omit [DecidableEq d.Ty] in
/-- Every terminator and every op with no callee of a valid function is
monotone with memory, when every such op is at every valid op instance. -/
theorem Func.Valid.memOpsMonotone
    (hmono : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
      OpMemMonotone (σ := Memories Mem unit) op)
    {ctx : ModuleContext d} {f : Func d} (hv : f.Valid ctx) : f.MemOpsMonotone Mem unit :=
  fun _ hb o ho => hmono o.op (hv.typesValid hb ho)

end

/-! # What the class gives -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] [DialectValidation d] [TyRefinement d.Ty]
  [LawfulDialectMonotone d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d} {M : Module d}

/-- Refined arguments and memories, by the class alone: in a module whose
functions are all valid, a function's behaviour from memories that refine
others, on arguments that refine others, refines its behaviour from those
others, the memories they end with included, wherever a run names the
dialect's memories, calls and recursion included. -/
theorem Func.memRunsFrom_args_isRefinedBy_of_lawful (hv : ∀ g ∈ M.funcs, g.Valid ctx)
    {f : Func d} (hf : f ∈ M.funcs) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {S S' : Memories N (unitsOf lay)} (hS : S ⊑ S') :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M (a', S')) :=
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  have hmono := fun g (hg : g ∈ M.funcs) => (hv g hg).memOpsMonotone
    (fun op hvo hc => LawfulDialectMonotone.monotone op hvo hc lay ρ)
  Func.memRunsFrom_args_isRefinedBy M hmono f (hmono f hf) ha hS

/-- Refined arguments, with memory, by the class alone: in a module whose
functions are all valid, a function's behaviour with memory on arguments
that refine others, a poison by any value, refines its behaviour with
memory on those others, wherever a run names the dialect's memories, calls
and recursion included, whatever its ops do to the memories. -/
theorem Func.memRuns_args_isRefinedBy_of_lawful (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func d}
    (hf : f ∈ M.funcs) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ M a) ⊑ observable (f.memRuns lay ρ M a') :=
  Func.memRuns_isRefinedBy_of_from lay ρ
    (Func.memRunsFrom_args_isRefinedBy_of_lawful lay ρ hv hf ha (Memories.isRefinedBy_refl _))

/-- Congruence in the callee, with memory, by the class alone: in a valid
module, replacing the body of its function `@g` with one under which `@g`,
run in the new module from given memories, refines `@g` in the old, refines
every function of the module, from given memories and so with memory,
wherever a run names the dialect's memories, calls and recursion included,
whatever the new body. It asks what the theorem on runs from given
memories asks, the budget for the new `@g` included. -/
theorem Func.memRuns_replaceBody_isRefinedBy_of_bound
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hbound : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    (letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      f.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (f.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b)) ∧
      f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  have hmono := fun g (hg : g ∈ M.funcs) => (hM.funcs g hg).memOpsMonotone
    (fun op hvo hc => LawfulDialectMonotone.monotone op hvo hc lay ρ)
  have hr := Func.memRunsFrom_replaceBody_isRefinedBy hmono hrefl htrans hM.symbolsUnique hg b
    hbound h hf
  exact ⟨hr, fun a => Func.memRuns_isRefinedBy_of_from lay ρ (hr (a, Memories.empty))⟩

end Fir
