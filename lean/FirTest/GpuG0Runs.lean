import FirTest.G0

/-!
G0's results on runs, refinement and congruence restated for a dialect set
that includes `gpu` (ADR-2026-11-09-1545, stage 4 of the stage plan on
#212), split from `FirTest.GpuG0` by subject. Each statement applies the
theorem of `FirTest.G0` that states the result for every dialect, at the
sum of the core and `gpu`, `CoreGpu`, or at the core as a base with `gpu`'s
extension, `GpuExt`, at every work-item and wherever a run names the sum's
memories. The sum meets each hypothesis with no assumption of its own:

* it is lawful in its totality, its monotonicity and its poison with
  memory (`Gpu.coreGpu_lawfulTotal`, `coreGpu_lawfulMonotone`,
  `coreGpu_lawfulMemPoison`), by the theorems for every sum restated
  below;
* a valid function of the sum runs within its module, with memory
  (`Gpu.inModule_of_valid`, `Gpu.inModuleAt_of_valid`);
* each of its ops that runs by its own rule is monotone with memory, has
  finitely many outcomes, and ignores the memories where it touches none
  (`Gpu.memMonotone_all`, `Gpu.opsFinite`, `Gpu.opsIgnoreMemory`).

A result about the functions of a module holds for the functions of each
symbol table of a valid module, nested at any depth, run in the module of
that table (`Module.nest`): a device module's kernels are among them.
-/

namespace FirTest.GpuG0

open Fir Fir.Gpu Fir.Memory

variable [WorkItem]

/-! # Execution -/

/-- More fuel never changes how a run of a function of the sum ends, in the
set monad. -/
theorem fuelMonotone (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.runs M args) :=
  G0.fuelMonotone CoreGpu M f args

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreGpu → N)

/-- More fuel never changes how a run with memory of a function of the sum
ends. -/
theorem memRuns_fuelMonotone (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ M args) :=
  G0.memRuns_fuelMonotone CoreGpu lay ρ M f args

variable {M : Module CoreGpu} {t : SymbolTable CoreGpu} {f : Func CoreGpu}

omit [DecidableEq N] in
/-- No path of a run in the set monad of a function of each table of a valid
module of the sum, in the module of its table, is stuck. -/
theorem neverStuck (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.runs (M.nest t) args) :=
  G0.neverStuck CoreGpu (hM.nest ht).funcs (fun _ hg => inModule_of_valid ((hM.nest ht).funcs _ hg))
    hf args

/-- No path of a run with memory of a function of each table of a valid
module of the sum, in the module of its table, is stuck. -/
theorem memNeverStuck (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) :
    NeverStuck (f.memRuns lay ρ (M.nest t) args) :=
  G0.memNeverStuck CoreGpu lay ρ (hM.nest ht).funcs
    (fun _ hg => inModuleAt_of_valid lay ρ ((hM.nest ht).funcs _ hg)) hf args

/-- A run with memory of a function of each table of a valid module of the
sum, in the module of its table, has an outcome at every budget. -/
theorem memProgress (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) :
    Progress (f.memRuns lay ρ (M.nest t) args) :=
  G0.memProgress CoreGpu lay ρ (hM.nest ht).funcs
    (fun _ hg => inModuleAt_of_valid lay ρ ((hM.nest ht).funcs _ hg)) hf args

/-! # Refinement with memory -/

/-- Refined arguments and memories, for every function of every module of
the sum: from memories that refine others, on arguments that refine others,
its behaviour refines its behaviour from those others. -/
theorem memRunsFrom_args_isRefinedBy (M : Module CoreGpu) (f : Func CoreGpu)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories N (unitsOf lay)} (hS : S ⊑ S') :
    letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M (a', S')) :=
  letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
  have hm : ∀ g : Func CoreGpu, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => memMonotone_all o.op hc lay ρ
  G0.memRunsFrom_args_isRefinedBy CoreGpu M (fun g _ => hm g) f (hm f) ha hS

/-- Refined arguments, with memory, for every function of each table of a
valid module of the sum, in the module of its table. -/
theorem memRuns_args_isRefinedBy (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ (M.nest t) a) ⊑ observable (f.memRuns lay ρ (M.nest t) a') :=
  G0.memRuns_args_isRefinedBy CoreGpu lay ρ (hM.nest ht).funcs hf ha

omit [WorkItem] in
/-- Refinement of values of the sum is reflexive. -/
theorem isRefinedBy_refl {u : CoreGpu.Ty} (v : ⟦u⟧) : TyRefinement.IsRefinedBy v v :=
  Dialect.sum.isRefinedBy_refl (e := GpuExt) Core.Ty.isRefinedBy_refl (fun {t} => Empty.elim t) v

omit [WorkItem] in
/-- Refinement of values of the sum is transitive. -/
theorem isRefinedBy_trans {u : CoreGpu.Ty} {x y z : ⟦u⟧} (h₁ : TyRefinement.IsRefinedBy x y)
    (h₂ : TyRefinement.IsRefinedBy y z) : TyRefinement.IsRefinedBy x z :=
  Dialect.sum.isRefinedBy_trans (e := GpuExt) Core.Ty.isRefinedBy_trans (fun {t} => Empty.elim t)
    h₁ h₂

/-- Congruence in the callee, with memory, in the module of each table of a
valid module of the sum, when the new body, run from given memories,
refines the old one and has one budget past which it runs out of fuel only
if it diverges. -/
theorem memRuns_replaceBody_isRefinedBy (hM : M.Valid) (ht : t ∈ M.tables) {g : Func CoreGpu}
    (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (hbound : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        ((M.nest t).replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.memRuns lay ρ (M.nest t) ⊑
      (f.replaceBody g.name b).memRuns lay ρ ((M.nest t).replaceBody g.name b) :=
  G0.memRuns_replaceBody_isRefinedBy CoreGpu lay ρ isRefinedBy_refl isRefinedBy_trans (hM.nest ht)
    hg b hbound h hf

/-- Congruence in the callee, with memory, with no budget, in the module of
each table of a valid module of the sum: every op of the sum has finitely
many outcomes. -/
theorem memRuns_replaceBody_isRefinedBy_of_opsFinite (hM : M.Valid) (ht : t ∈ M.tables)
    {g : Func CoreGpu} (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.memRuns lay ρ (M.nest t) ⊑
      (f.replaceBody g.name b).memRuns lay ρ ((M.nest t).replaceBody g.name b) :=
  G0.memRuns_replaceBody_isRefinedBy_of_opsFinite CoreGpu lay ρ isRefinedBy_refl isRefinedBy_trans
    (opsFinite lay ρ) (hM.nest ht) hg b h hf

/-- Congruence in the callee, with memory, with no budget, in the module of
each table of a valid module of the sum, when the callee reaches no memory
before or after and the new body refines the old one with memory: every op
of the sum has finitely many outcomes and ignores the memories where it
touches none. -/
theorem memRuns_replaceBody_isRefinedBy_of_opsFinite_memRuns (hM : M.Valid) (ht : t ∈ M.tables)
    {g : Func CoreGpu} (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (hold : (M.nest t).table.ReachesNoMemory g.name)
    (hmem : ((M.nest t).replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ (M.nest t) ⊑
      (g.replaceBody g.name b).memRuns lay ρ ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.memRuns lay ρ (M.nest t) ⊑
      (f.replaceBody g.name b).memRuns lay ρ ((M.nest t).replaceBody g.name b) :=
  G0.memRuns_replaceBody_isRefinedBy_of_opsFinite_memRuns CoreGpu lay ρ isRefinedBy_refl
    isRefinedBy_trans (opsIgnoreMemory lay ρ) (opsFinite lay ρ) (hM.nest ht) hg b hold hmem h hf

/-- Refinement from given memories with black boxes that need no budget,
for every function of every module of the sum. -/
theorem memRunsFrom_isRefinedBy_of_opsFinite {M M' : Module CoreGpu}
    (hcalls : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
      MemCallsRefined N (unitsOf lay) M M')
    (f : Func CoreGpu) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') {S S' : Memories N (unitsOf lay)} (hS : S ⊑ S') :
    letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M' (a', S')) :=
  letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
  have hm : ∀ g : Func CoreGpu, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => memMonotone_all o.op hc lay ρ
  G0.memRunsFrom_isRefinedBy_of_opsFinite CoreGpu (fun g _ => hm g) (opsFinite lay ρ) hcalls f
    (hm f) ha hS

/-! # The obligations -/

/-- The sum of the core and `gpu` is lawful in its monotonicity, by the
theorem for every sum. -/
theorem sum_lawfulMonotone : LawfulDialectMonotone (CoreDialect ⊞ GpuExt) :=
  G0.sum_lawfulMonotone CoreDialect GpuExt fun _ h => h

/-- The sum of the core and `gpu` is lawful in its poison with memory, by
the theorem for every sum. -/
theorem sum_lawfulMemPoison : LawfulDialectMemPoison (CoreDialect ⊞ GpuExt) :=
  G0.sum_lawfulMemPoison CoreDialect GpuExt fun _ h => h

end FirTest.GpuG0
