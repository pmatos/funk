import Fir
import FirRef

/-!
G0's check on the Lean side, for refinement of runs with memory
(ADR-2026-11-03-0600,
`docs/decisions/semantics-refinement.md#refinement-with-memory`), split from `FirTest.G0` by
subject. Each statement below is made of an arbitrary dialect `d`, or an
arbitrary base and extension, with the spec's own proof, so it builds only
while those stay parameterized over the dialect. `scripts/check_g0.py`
checks this file as it checks the other files of `FirTest/G0/`, outside its
`#guard` commands.

They restate, for runs with memory, the refinement results: refined
arguments and memories, and congruence in the callee, for every dialect
lawful in its monotonicity with memory, whatever its ops do to the
memories, with a budget for the new callee or, when the dialect's ops have
finitely many outcomes, with none, from given memories or, for a callee
that reaches no memory, with memory; and the obligation itself, which every
lawful dialect that lifts the set monad meets, and which sums and lifts
keep.
-/

namespace FirTest.G0

open Fir Fir.Memory

/-! # Refinement with memory -/

/-- Refined arguments and memories, for every function of every module of
every dialect whose ops that run by their own rule are monotone with
memory: from memories that refine others, on arguments that refine others,
its behaviour refines its behaviour from those others, the memories they
end with included. -/
theorem memRunsFrom_args_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [TyRefinement d.Ty] {N : Type} [DecidableEq N]
    {unit : N → Nat} [DialectDenote d (StateT (Memories N unit) SetM)] (M : Module d)
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone N unit) (f : Func d) (hf : f.MemOpsMonotone N unit)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories N unit} (hS : S ⊑ S') :
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M (a', S')) :=
  Func.memRunsFrom_args_isRefinedBy M hmono f hf ha hS

/-- Refined arguments, with memory, for every function of a module whose
functions are valid, of every dialect lawful in its monotonicity, wherever
a run names its memories. -/
theorem memRuns_args_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [LawfulDialectMonotone d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) {ctx : ModuleContext d}
    {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func d} (hf : f ∈ M.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ M a) ⊑ observable (f.memRuns lay ρ M a') :=
  Func.memRuns_args_isRefinedBy_of_lawful lay ρ hv hf ha

/-- Congruence in the callee, with memory, for every function of a valid
module of every dialect lawful in its monotonicity, wherever a run names
its memories, when the new body, run from given memories, refines the old
one and has one budget past which it runs out of fuel only if it
diverges. -/
theorem memRuns_replaceBody_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [LawfulDialectMonotone d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hbound : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_bound lay ρ hrefl htrans hM hg b hbound h hf).2

/-- Congruence in the callee, with memory, with no budget, for every
function of a valid module of every dialect lawful in its monotonicity whose
ops that run by their own rule have finitely many outcomes, wherever a run
names its memories, when the new body, run from given memories, refines the
old one, whatever the parameter types of the callee and whatever its new
body does to the memories. -/
theorem memRuns_replaceBody_isRefinedBy_of_opsFinite (d : Dialect) [TyDenote d.Ty]
    [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [LawfulDialectMonotone d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfin : letI := DialectMemDenote.denoteAt (d := d) lay ρ; OpsFinite d N (unitsOf lay))
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ hrefl htrans hfin hM hg b h hf).2

/-- Congruence in the callee, with memory, with no budget, for every
function of a valid module of every dialect lawful in its monotonicity whose
ops that run by their own rule have finitely many outcomes, and ignore the
memories where they touch none, wherever a run names its memories, when the
callee reaches no memory before or after and the new body refines the old
one with memory, whatever the parameter types of the callee. -/
theorem memRuns_replaceBody_isRefinedBy_of_opsFinite_memRuns (d : Dialect) [TyDenote d.Ty]
    [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [LawfulDialectMonotone d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfree : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      OpsIgnoreMemory d N (unitsOf lay))
    (hfin : letI := DialectMemDenote.denoteAt (d := d) lay ρ; OpsFinite d N (unitsOf lay))
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hold : M.table.ReachesNoMemory g.name)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  Func.memRuns_replaceBody_isRefinedBy_of_opsFinite_memRuns lay ρ hrefl htrans hfree hfin hM hg b
    hold hmem h hf

/-- Refinement from given memories with black boxes that need no budget, for
every function of every module of every dialect whose ops that run by their
own rule have finitely many outcomes and are monotone with memory. -/
theorem memRunsFrom_isRefinedBy_of_opsFinite (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [TyRefinement d.Ty] {N : Type} [DecidableEq N]
    {unit : N → Nat} [DialectDenote d (StateT (Memories N unit) SetM)] {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone N unit) (hfin : OpsFinite d N unit)
    (hcalls : MemCallsRefined N unit M M') (f : Func d) (hf : f.MemOpsMonotone N unit)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories N unit} (hS : S ⊑ S') :
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M' (a', S')) :=
  Func.memRunsFrom_isRefinedBy_of_opsFinite hmono hfin hcalls f hf ha hS

/-! # The obligation -/

/-- Every lawful dialect that lifts the set monad is lawful in its
monotonicity. -/
theorem lawfulMonotone_ofLawful (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d] [LawfulDialectPoison d] :
    LawfulDialectMonotone d :=
  LawfulDialectMonotone.ofLawful

/-- Every sum of two dialects lawful in their monotonicity is lawful in its
monotonicity, when the extension accepts the base's valid types. Neither
side needs a semantics in the set monad. -/
theorem sum_lawfulMonotone (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty]
    [TyRefinement base.Ty] [TyRefinement e.Ty] [DialectSignature base]
    [DialectSignature (base.over e)] [DialectEffects base] [DialectEffects (base.over e)]
    [DialectMemOver base e] [DialectMemDenote base] [DialectMemDenote (base.over e)]
    [DialectCall base] [DialectCall (base.over e)] [DialectValidation base]
    [DialectValidation (base.over e)] [LawfulDialectMonotone base]
    [LawfulDialectMonotone (base.over e)]
    (hty : ∀ t : base.Ty, validTy t → validTy (d := base.over e) (.inl t)) :
    LawfulDialectMonotone (base ⊞ e) :=
  Dialect.sum.lawfulMonotone hty

end FirTest.G0
