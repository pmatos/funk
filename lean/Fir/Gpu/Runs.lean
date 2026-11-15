import Fir.Gpu.Semantics
import Fir.Sum.RunLaws
import Fir.Sum.TotalLaws
import Fir.Sum.MonotoneLaws
import Fir.Sum.MemPoisonLaws
import Fir.Core.MemoryCallRefine
import Fir.Validation.Nest
import Fir.Sum.TextLaws

/-!
# Every valid function of the core and `gpu`

The sum of the core and `gpu`, `CoreGpu`, keeps every guarantee of the
whole core with memory (`docs/decisions/semantics-m1-memory.md#the-cores-guarantees`),
at every work-item, and for the functions of every symbol table of a valid
module: its own, and that of each module nested in it at any depth, such as a
device module's kernels. A function of a nested table runs in the module of
its table (`Module.nest`): a call names a function of that table, and its
memories are those of the host's data layout.

* _The sum is lawful in its effects, its totality, its monotonicity and its
  poison with memory_, since both sides are (the sections on sums), and
  `gpu` accepts each type the core accepts.
* _Every function of each table of a valid module runs well with memory_:
  its runs are fuel-monotone, as those of every function are, have an
  outcome at every budget, and have no stuck path, calls and recursion
  included. A valid function of the sum
  runs within its module: validation's rule for a core op in the sum is
  the core's rule over the symbols whose types are all the core's, so a
  `call` names a function of the module of its type, and the core's
  terminators keep to their rules. Every terminator is the core's, and is
  tied to the set monad.
* _Refined arguments_: on arguments that refine others, the runs with
  memory of every function of every module of the sum refine its runs on
  those others: every op of the sum that runs by its own rule is monotone
  with memory, at every width.
* _Congruence in the callee_, from given memories, with no budget, for every
  callee of the module of each table of a valid module: every op of the sum
  has finitely many outcomes, an op of `gpu` one.
-/

namespace Fir.Gpu

variable [WorkItem]

/-- The sum is lawful in its effects, since both sides are. -/
instance coreGpu_lawfulEffects : LawfulDialectEffects CoreGpu :=
  Dialect.sum.lawfulEffects fun _ h => h

/-- The sum is lawful in its totality, since both sides are. -/
instance coreGpu_lawfulTotal : LawfulDialectTotal CoreGpu :=
  Dialect.sum.lawfulTotal fun _ h => h

/-- The sum is lawful in its monotonicity, since both sides are. -/
instance coreGpu_lawfulMonotone : LawfulDialectMonotone CoreGpu :=
  Dialect.sum.lawfulMonotone fun _ h => h

/-- The sum is lawful in its poison with memory, since both sides are. -/
instance coreGpu_lawfulMemPoison : LawfulDialectMemPoison CoreGpu :=
  Dialect.sum.lawfulMemPoison fun _ h => h

/-- Every op of `gpu` is monotone with memory, at every width. -/
theorem Op.memMonotone (op : Op) : MemMonotone (d := GpuDialect) op :=
  MemMonotone.ofLifts (LiftsSetM.opLifts (d := GpuDialect) op) (Op.monotone op)

/-- Every op of the sum that runs by its own rule is monotone with memory, at
every width, valid or not. -/
theorem memMonotone_all :
    ∀ op : CoreGpu.Op, isTerminator op = true ∨ callee? op = none → MemMonotone op
  | .inl o, hc => Dialect.sum.memMonotone_inl (Core.Op.memMonotone_all o hc)
  | .inr o, _ => Op.memMonotone o

/-- A valid function of the sum runs within its module: a `call` names a
function of the module of its type, and the core's terminators keep to
their rules. -/
theorem inModule_of_valid {M : Module CoreGpu} {f : Func CoreGpu} (hv : f.Valid M.context) :
    f.InModule M where
  calls b hb o ho _ s h := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hvalid : validOp ⟨M.context.symbols, f.results⟩ b.body[i].op :=
      (hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)).2.2.2.2.2.2.2.2.2.1
    generalize b.body[i].op = op at h hvalid ⊢
    rcases op with op | op
    · obtain ⟨ts, rs, rfl⟩ := Core.Op.eq_call_of_callee h
      change Dialect.sum.BaseValidOp _ _ at hvalid
      unfold Dialect.sum.BaseValidOp Dialect.sum.baseContext at hvalid
      split at hvalid
      · rename_i c hc
        obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨t, ht, hb⟩ := Option.bind_eq_some_iff.mp hvalid
        obtain ⟨ps, hps, hb⟩ := Option.bind_eq_some_iff.mp hb
        obtain ⟨rs', hrs, hb⟩ := Option.bind_eq_some_iff.mp hb
        cases hb
        change M.symbols s = some t at ht
        rw [ht]
        obtain ⟨tp, tr⟩ := t
        change tp.mapM _ = _ at hps
        change tr.mapM _ = _ at hrs
        rw [Dialect.sum.eq_map_of_mapM_getLeft hps, Dialect.sum.eq_map_of_mapM_getLeft hrs]
        rfl
      · exact hvalid.elim
    · cases op; cases h
  jumps _ _ o _ hT args i h := by
    generalize o.op = op at hT args h ⊢
    rcases op with op | op
    · obtain ⟨hlt, hr⟩ := Core.Op.exit_goto op _ hT h
      exact ⟨hlt, by change (returnTypes op).map _ = []; rw [hr]; rfl⟩
    · cases op; cases hT
  returns b hb o ho hT args h := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hvalid : validOp ⟨M.context.symbols, f.results⟩ b.body[i].op :=
      (hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)).2.2.2.2.2.2.2.2.2.1
    generalize b.body[i].op = op at hT args h hvalid ⊢
    rcases op with op | op
    · obtain ⟨ts, rfl⟩ := Core.Op.exit_ret op _ h
      change Dialect.sum.BaseValidOp _ _ at hvalid
      unfold Dialect.sum.BaseValidOp Dialect.sum.baseContext at hvalid
      split at hvalid
      · rename_i c hc
        obtain ⟨rs, hrs, rfl⟩ := Option.map_eq_some_iff.mp hc
        change ts = rs at hvalid
        subst hvalid
        exact (Dialect.sum.eq_map_of_mapM_getLeft hrs).symm
      · exact hvalid.elim
    · cases op; cases hT

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreGpu → N)

/-- A valid function of the sum runs within its module with memory, wherever
a run names the sum's memories: each of its terminators is the core's, and
is tied. -/
theorem inModuleAt_of_valid {M : Module CoreGpu} {f : Func CoreGpu} (hv : f.Valid M.context) :
    f.InModuleAt lay ρ M :=
  (inModule_of_valid hv).inModuleAt_of_tied lay ρ fun _ _ o _ hT => by
    rcases ho : o.op with op | op
    · rw [ho] at hT
      exact Dialect.sum.opLiftsSetM_inl (Core.Op.liftsSetM_of_terminator hT)
    · rw [ho] at hT; cases op; cases hT

variable {M : Module CoreGpu} {t : SymbolTable CoreGpu} {f : Func CoreGpu}

/-- More fuel never changes how a run with memory of a function of every
module of the sum returns or hits UB, calls and recursion included. -/
theorem fuelMonotone (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ M args) :=
  Func.memRuns_fuelMonotone lay ρ M f args

/-- A run with memory of every function of each table of a valid module of
the sum, nested at any depth, in the module of its table, has an outcome at
every budget, calls and recursion included, wherever a run names the sum's
memories. -/
theorem progress (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ (M.nest t) args) :=
  have hN := hM.nest ht
  Func.memProgress lay ρ hN.funcs (fun _ hg => inModuleAt_of_valid lay ρ (hN.funcs _ hg)) hf args

/-- No path of a run with memory of a function of each table of a valid
module of the sum, in the module of its table, is stuck, calls and
recursion included. -/
theorem neverStuck (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ (M.nest t) args) :=
  have hN := hM.nest ht
  Func.memNeverStuck lay ρ hN.funcs (fun _ hg => inModuleAt_of_valid lay ρ (hN.funcs _ hg)) hf
    args

/-- Refined arguments, with memory: on arguments that refine others, the runs
with memory of every function of every module of the sum, a module of a
nested table included, refine its runs on those others, calls and recursion
included, wherever a run names the sum's memories. -/
theorem args_isRefinedBy (M : Module CoreGpu) (f : Func CoreGpu)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ M a) ⊑ observable (f.memRuns lay ρ M a') :=
  letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
  have hm : ∀ g : Func CoreGpu, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => memMonotone_all o.op hc lay ρ
  Func.memRuns_isRefinedBy_of_from lay ρ (Func.memRunsFrom_args_isRefinedBy M (fun g _ => hm g) f
    (hm f) h (Memory.Memories.isRefinedBy_refl _))

/-- Each op of `gpu` has one outcome with memory, at every layout and naming. -/
theorem opsFinite_gpu (ρ : DialectEffects.Mem GpuDialect → N) :
    letI := DialectMemDenote.denoteAt (d := GpuDialect) lay ρ
    OpsFinite GpuDialect N (unitsOf lay) := fun op _ _ =>
  ⟨fun _ => FinitelyMany.lift ⟨[op.results], fun _ h => by cases h; exact List.mem_singleton_self _⟩,
    fun h => by cases op; cases h⟩

/-- Every op of the sum that runs by its own rule has finitely many outcomes
with memory, at every layout and naming. -/
theorem opsFinite :
    letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ
    OpsFinite CoreGpu N (unitsOf lay) :=
  Dialect.sum.opsFinite lay ρ (Core.opsFinite lay _) (opsFinite_gpu lay ρ)

/-- Congruence in the callee, with memory: in the module of each table of a
valid module of the sum, replacing the body of a function `@g` with one under
which `@g`, run in the new module from given memories, refines `@g` in the
old, refines every function of the table with memory, calls and recursion
included, wherever a run names the sum's memories. It asks for no budget,
whatever the parameter types of `@g` and whatever its new body does to the
memories: every op of the sum has finitely many outcomes. -/
theorem replaceBody_isRefinedBy_of_from (hM : M.Valid) (ht : t ∈ M.tables) {g : Func CoreGpu}
    (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.memRuns lay ρ (M.nest t) ⊑
      (f.replaceBody g.name b).memRuns lay ρ ((M.nest t).replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ
    (Dialect.sum.isRefinedBy_refl (e := GpuExt) Core.Ty.isRefinedBy_refl fun {t} => Empty.elim t)
    (Dialect.sum.isRefinedBy_trans (e := GpuExt) Core.Ty.isRefinedBy_trans fun {t} => Empty.elim t)
    (opsFinite lay ρ) (hM.nest ht) hg b h hf).2

end Fir.Gpu
