import FirTest.G0Effects

/-!
G0's results on effects and function summaries restated for a dialect set
that includes `gpu` (ADR-2026-11-09-1545, stage 4 of the stage plan on
#212), split from `FirTest.GpuG0` by subject. Each statement applies the
theorem of `FirTest.G0` that states the result for every dialect, at the
sum of the core and `gpu`, `CoreGpu`, or at the core as a base with `gpu`'s
extension, `GpuExt`, at every work-item. The sum meets each hypothesis with
no assumption of its own: it is lawful in its effects and its totality
(`Gpu.coreGpu_lawfulEffects`, `Gpu.coreGpu_lawfulTotal`). A summary's
results hold for the functions of each symbol table of a valid module,
nested at any depth, in the module of that table.
-/

namespace FirTest.GpuG0

open Fir Fir.Gpu

variable [WorkItem]

/-! # Effects -/

/-- In the sum, a valid op that runs by its own rule and does not declare
may-UB never ends in UB. -/
theorem neverUB (op : CoreGpu.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (h : (effects op).mayUB = false) :
    NeverUB op :=
  G0.neverUB CoreGpu op hv hc h

/-- In the sum, a valid op that runs by its own rule and does not declare
that it may produce poison makes none. -/
theorem makesNoPoison (op : CoreGpu.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (h : (effects op).mayPoison = false) :
    MakesNoPoison op :=
  G0.makesNoPoison CoreGpu op hv hc h

/-- In the sum, an op that does not declare control is not a terminator. -/
theorem notControl (op : CoreGpu.Op) (h : (effects op).control = false) :
    isTerminator op = false :=
  G0.notControl CoreGpu op h

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreGpu → N)

/-- In the sum, a valid op that runs by its own rule and does not declare a
write to a memory of a run writes no unit of it, wherever the run names the
sum's memories. -/
theorem writesNot (op : CoreGpu.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (x : N)
    (h : ¬ ((effects op).writes.map ρ).Has x) : OwnRuleHas lay ρ (WritesNot x) op :=
  G0.writesNot CoreGpu op hv hc lay ρ x h

/-- In the sum, a valid op that runs by its own rule and does not declare a
read of a memory of a run does not depend on its units. -/
theorem readsNot (op : CoreGpu.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (x : N)
    (h : ¬ ((effects op).reads.map ρ).Has x) : OwnRuleHas lay ρ (ReadsNot x) op :=
  G0.readsNot CoreGpu op hv hc lay ρ x h

/-- In the sum, a valid op that runs by its own rule and does not declare
allocation in a memory of a run leaves its allocations as they were; so a
question of `gpu` allocates in no memory, and `gpu.work_group_alloca` only
in the memory of its result. -/
theorem allocatesNot (op : CoreGpu.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) (x : N)
    (h : ¬ ((effects op).allocates.map ρ).Has x) : OwnRuleHas lay ρ (AllocatesNot x) op :=
  G0.allocatesNot CoreGpu op hv hc lay ρ x h

/-- In the sum, a valid op that runs by its own rule has an outcome from
any memories. -/
theorem memTotal (op : CoreGpu.Op) (hv : TypesValid op)
    (hc : isTerminator op = true ∨ callee? op = none) : OwnRuleHas lay ρ HasOutcome op :=
  G0.memTotal CoreGpu op hv hc lay ρ

/-- The sum of the core and `gpu` is lawful in its totality, by the theorem
for every sum. -/
theorem sum_lawfulTotal : LawfulDialectTotal (CoreDialect ⊞ GpuExt) :=
  G0.sum_lawfulTotal CoreDialect GpuExt fun _ h => h

/-- In the sum, the memories are `gpu`'s, which are the core's. -/
example : DialectEffects.Mem (CoreDialect ⊞ GpuExt) = DialectEffects.Mem GpuDialect := rfl

omit [WorkItem] in
/-- In a lift of `gpu` over a larger base, `gpu`'s name for a memory of the
core becomes that memory's name in the larger base. -/
theorem liftMem_ofBase (big : Dialect) [TyDenote big.Ty] [DialectEffects big]
    (μ : DialectEffects.Mem CoreDialect → DialectEffects.Mem big)
    (a : DialectEffects.Mem CoreDialect) :
    Dialect.lift.liftMem (e := GpuExt) μ (DialectMemOver.ofBase a) = .inl (μ a) :=
  G0.liftMem_ofBase GpuExt CoreDialect big μ a

/-! # Summaries -/

omit [WorkItem] in
/-- In the sum, the summary is the least assignment closed under the calls
of a table. -/
theorem summary_least (t : SymbolTable CoreGpu) : t.Closed t.summary ∧
    ∀ T : Name → Effects (DialectEffects.Mem CoreGpu), t.Closed T → ∀ s, t.summary s ≤ T s :=
  G0.summary_least CoreGpu t

variable {M : Module CoreGpu} {t : SymbolTable CoreGpu}

/-- A function of each table of a valid module of the sum, nested at any
depth, whose summary leaves out may-UB never ends in UB in its runs with
memory, in the module of its table. -/
theorem summary_neverUB (hM : M.Valid) (ht : t ∈ M.tables) {s : Name} {f : Func CoreGpu}
    (hf : (M.nest t).func? s = some f) (hs : ((M.nest t).table.summary s).mayUB = false)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (r : String) :
    ¬ f.memRuns lay ρ (M.nest t) args fuel (.ub r) :=
  G0.summary_neverUB CoreGpu lay ρ (hM.nest ht).funcs hf hs args fuel r

/-- A function of each table of a valid module of the sum whose summary
leaves out may produce poison returns no poison on arguments with none, in
its runs with memory, in the module of its table. -/
theorem summary_noPoison (hM : M.Valid) (ht : t ∈ M.tables) {s : Name} {f : Func CoreGpu}
    (hf : (M.nest t).func? s = some f) (hs : ((M.nest t).table.summary s).mayPoison = false)
    (args : HVector toType (f.params.map (·.2))) (hargs : ¬ args.Any TyPoison.IsPoison)
    (fuel : Nat) (vs : List (DVal CoreGpu)) :
    f.memRuns lay ρ (M.nest t) args fuel (.ok (.ok (.ret vs))) → DVals.Clean vs :=
  G0.summary_noPoison CoreGpu lay ρ (hM.nest ht).funcs hf hs args hargs fuel vs

end FirTest.GpuG0
