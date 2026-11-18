import Fir.Gpu.WorkGroup
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
  has finitely many outcomes, an op of `gpu` one. Every other function of
  the table, a caller or not, is refined by itself.
* _Congruence for a callee that reaches no memory_, with memory, with no
  budget: the sum's ops also ignore the memories where they touch none, a
  question of `gpu` since it touches none and keeps them, while an
  allocation declares its memory.
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
    · cases op <;> cases h
  jumps _ _ o _ hT args i h := by
    generalize o.op = op at hT args h ⊢
    rcases op with op | op
    · obtain ⟨hlt, hr⟩ := Core.Op.exit_goto op _ hT h
      exact ⟨hlt, by change (returnTypes op).map _ = []; rw [hr]; rfl⟩
    · cases op <;> cases hT
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
    · cases op <;> cases hT

omit [WorkItem] in
/-- Refinement of values of the sum is reflexive, since the core's is and
`gpu` has no type of its own. -/
theorem isRefinedBy_refl {u : CoreGpu.Ty} (v : ⟦u⟧) : TyRefinement.IsRefinedBy v v :=
  Dialect.sum.isRefinedBy_refl (e := GpuExt) Core.Ty.isRefinedBy_refl (fun {t} => Empty.elim t) v

omit [WorkItem] in
/-- Refinement of values of the sum is transitive, since the core's is and
`gpu` has no type of its own. -/
theorem isRefinedBy_trans {u : CoreGpu.Ty} {x y z : ⟦u⟧} (h₁ : TyRefinement.IsRefinedBy x y)
    (h₂ : TyRefinement.IsRefinedBy y z) : TyRefinement.IsRefinedBy x z :=
  Dialect.sum.isRefinedBy_trans (e := GpuExt) Core.Ty.isRefinedBy_trans (fun {t} => Empty.elim t)
    h₁ h₂

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreGpu → N) (L :
    RunItems)

/-- Each op of every function of the sum that runs by its own rule is
monotone with memory, at every layout and naming. -/
theorem memOpsMonotone (g : Func CoreGpu) :
    letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L
    g.MemOpsMonotone N (unitsOf lay) :=
  fun _ _ o _ hc => memMonotone_all o.op hc lay ρ L

/-- A valid function of the sum runs within its module with memory, wherever
a run names the sum's memories: each of its terminators is the core's, and
is tied. -/
theorem inModuleAt_of_valid {M : Module CoreGpu} {f : Func CoreGpu} (hv : f.Valid M.context) :
    f.InModuleAt lay ρ L M :=
  (inModule_of_valid hv).inModuleAt_of_tied lay ρ L fun _ _ o _ hT => by
    rcases ho : o.op with op | op
    · rw [ho] at hT
      exact Dialect.sum.opLiftsSetM_inl (Core.Op.liftsSetM_of_terminator hT)
    · rw [ho] at hT; cases op <;> cases hT

variable {M : Module CoreGpu} {t : SymbolTable CoreGpu} {f : Func CoreGpu}

/-- More fuel never changes how a run with memory of a function of every
module of the sum returns or hits UB, calls and recursion included. -/
theorem fuelMonotone (M : Module CoreGpu) (f : Func CoreGpu)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ L M args) :=
  Func.memRuns_fuelMonotone lay ρ L M f args

/-- A run with memory of every function of each table of a valid module of
the sum, nested at any depth, in the module of its table, has an outcome at
every budget, calls and recursion included, wherever a run names the sum's
memories. -/
theorem progress (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ L (M.nest t) args) :=
  have hN := hM.nest ht
  Func.memProgress lay ρ L hN.funcs (fun _ hg => inModuleAt_of_valid lay ρ L (hN.funcs _ hg)) hf
      args

/-- No path of a run with memory of a function of each table of a valid
module of the sum, in the module of its table, is stuck, calls and
recursion included. -/
theorem neverStuck (hM : M.Valid) (ht : t ∈ M.tables) (hf : f ∈ t.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ L (M.nest t) args) :=
  have hN := hM.nest ht
  Func.memNeverStuck lay ρ L hN.funcs (fun _ hg => inModuleAt_of_valid lay ρ L (hN.funcs _ hg)) hf
    args

/-- Refined arguments, with memory: on arguments that refine others, the runs
with memory of every function of every module of the sum, a module of a
nested table included, refine its runs on those others, calls and recursion
included, wherever a run names the sum's memories. -/
theorem args_isRefinedBy (M : Module CoreGpu) (f : Func CoreGpu)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ L M a) ⊑ observable (f.memRuns lay ρ L M a') :=
  letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L
  Func.memRuns_isRefinedBy_of_from lay ρ L (Func.memRunsFrom_args_isRefinedBy M
    (fun g _ => memOpsMonotone lay ρ L g) f (memOpsMonotone lay ρ L f) h
    (Memory.Memories.isRefinedBy_refl _))

/-- Each op of `gpu` has one outcome with memory, at every layout and naming:
a question its results, and an allocation its one allocation. -/
theorem opsFinite_gpu (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems) :
    letI := DialectMemDenote.denoteAt (d := GpuDialect) lay ρ L
    OpsFinite GpuDialect N (unitsOf lay)
  | .query q d w, _, args => ⟨fun _ => by
      rw [(query_liftsSetM q d w lay ρ L args).1]
      exact FinitelyMany.lift
        ⟨[queryResults q d w], fun _ h => by cases h; exact List.mem_singleton_self _⟩,
    fun h => by cases h⟩
  | .alloc t c a n, _, args => ⟨fun _ => Op.alloc_finitelyMany t c a n lay ρ L args, fun h => by
      cases h⟩

/-- Every op of the sum that runs by its own rule has finitely many outcomes
with memory, at every layout and naming. -/
theorem opsFinite :
    letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L
    OpsFinite CoreGpu N (unitsOf lay) :=
  Dialect.sum.opsFinite lay ρ L (Core.opsFinite lay _ L) (opsFinite_gpu lay ρ L)

/-- Each op of `gpu` ignores the memories where it declares no memory
effect, at every layout and naming: a question runs by its rule in the set
monad and keeps the memories, and an allocation declares one. -/
theorem opsIgnoreMemory_gpu (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems) :
    letI := DialectMemDenote.denoteAt (d := GpuDialect) lay ρ L
    OpsIgnoreMemory GpuDialect N (unitsOf lay)
  | .query q d w, _, _ =>
    OwnRuleHas.ofLifts (query_liftsSetM q d w) lay ρ L (P := IgnoresMemory) IgnoresMemory.lift
  | .alloc _ _ _ n, _, h => absurd (List.mem_singleton_self _) ((h (.inl n)).2.2)

/-- Every op of the sum that runs by its own rule ignores the memories where
it declares no memory effect, at every layout and naming. -/
theorem opsIgnoreMemory :
    letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L
    OpsIgnoreMemory CoreGpu N (unitsOf lay) :=
  Dialect.sum.opsIgnoreMemory lay ρ L (Core.opsIgnoreMemory lay _ L)
    (opsIgnoreMemory_gpu lay ρ L)

/-- Congruence in the callee, with memory: in the module of each table of a
valid module of the sum, replacing the body of a function `@g` with one under
which `@g`, run in the new module from given memories, refines `@g` in the
old, refines every function of the table with memory, calls and recursion
included, wherever a run names the sum's memories. It asks for no budget,
whatever the parameter types of `@g` and whatever its new body does to the
memories: every op of the sum has finitely many outcomes. -/
theorem replaceBody_isRefinedBy_of_from (hM : M.Valid) (ht : t ∈ M.tables) {g : Func CoreGpu}
    (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.memRuns lay ρ L (M.nest t) ⊑
      (f.replaceBody g.name b).memRuns lay ρ L ((M.nest t).replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ L isRefinedBy_refl isRefinedBy_trans
    (opsFinite lay ρ L) (hM.nest ht) hg b h hf).2

/-- Every function of the table other than `@g`, a caller of it or not, is
refined with memory by itself in the module with `@g`'s new body, under the
hypotheses of congruence in the callee from given memories. -/
theorem caller_isRefinedBy_of_from (hM : M.Valid) (ht : t ∈ M.tables) {g : Func CoreGpu}
    (hg : g ∈ t.funcs) (b : Region CoreGpu)
    (h : letI := DialectMemDenote.denoteAt (d := CoreGpu) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) (M.nest t) ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ L (M.nest t) ⊑ f.memRuns lay ρ L ((M.nest t).replaceBody g.name b) := by
  have := replaceBody_isRefinedBy_of_from lay ρ L hM ht hg b h hf
  change f.memRuns lay ρ L (M.nest t) ⊑
    Func.memRuns lay ρ L _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

/-- Congruence in the callee, with memory, for a callee that reaches no
memory: in the module of each table of a valid module of the sum, replacing
the body of a function `@g`, which reaches no memory, with one under which
`@g`, run with memory in the new module, refines `@g` in the old, and under
which it reaches no memory in the new module, refines every function of the
table with memory, calls and recursion included, wherever a run names the
sum's memories. It asks for no budget and nothing of the parameter types of
`@g`: every op of the sum has finitely many outcomes and ignores the
memories where it touches none. -/
theorem replaceBody_isRefinedBy (hM : M.Valid) (ht : t ∈ M.tables) {g : Func CoreGpu}
    (hg : g ∈ t.funcs) (b : Region CoreGpu) (hold : (M.nest t).table.ReachesNoMemory g.name)
    (hmem : ((M.nest t).replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ L (M.nest t) ⊑
      (g.replaceBody g.name b).memRuns lay ρ L ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) :
    f.memRuns lay ρ L (M.nest t) ⊑
      (f.replaceBody g.name b).memRuns lay ρ L ((M.nest t).replaceBody g.name b) :=
  Func.memRuns_replaceBody_isRefinedBy_of_opsFinite_memRuns lay ρ L isRefinedBy_refl
    isRefinedBy_trans (opsIgnoreMemory lay ρ L) (opsFinite lay ρ L) (hM.nest ht) hg b hold hmem h hf

/-- Every function of the table other than `@g`, a caller of it or not, is
refined with memory by itself in the module with `@g`'s new body, under the
hypotheses of congruence in the callee for a callee that reaches no
memory. -/
theorem caller_isRefinedBy (hM : M.Valid) (ht : t ∈ M.tables) {g : Func CoreGpu}
    (hg : g ∈ t.funcs) (b : Region CoreGpu) (hold : (M.nest t).table.ReachesNoMemory g.name)
    (hmem : ((M.nest t).replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ L (M.nest t) ⊑
      (g.replaceBody g.name b).memRuns lay ρ L ((M.nest t).replaceBody g.name b))
    (hf : f ∈ t.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ L (M.nest t) ⊑ f.memRuns lay ρ L ((M.nest t).replaceBody g.name b) := by
  have := replaceBody_isRefinedBy lay ρ L hM ht hg b hold hmem h hf
  change f.memRuns lay ρ L (M.nest t) ⊑
    Func.memRuns lay ρ L _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

end Fir.Gpu
