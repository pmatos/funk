import Fir.Core.EffectLaws
import Fir.Core.CallRefine
import Fir.Execution.MemoryLocal
import Fir.Execution.MemoryRefineRuns
import Fir.Execution.MemoryPoison

/-!
# Every valid core function, with memory

Every core op but `alloca`, the loads `load`, `loadPtr` and `loadFloat`,
the stores `store`, `storePtr` and `storeFloat`, `memCopy` and `memSet`
touches no memory, and of those every op but `fieldAddr` reads no item of
the run either. Each op that touches no memory and reads no item runs with
memory by its rule in the set monad and keeps the memories, so it is tied
(the section on the core's rules with memory). So the core's obligations
with memory follow op by op (`Core.Op.memCases`), each from the op's own
tie and what the op meets in the set monad, and for `alloca`, the loads and
stores, `fieldAddr`, `memCopy` and `memSet` from their own rules with
memory (the sections on the stack allocation, load, store, field address,
copy and move, and fill obligations):

* _the core dialect is lawful in its totality_: each core terminator and
  each core op with no callee is total with memory: total in the set monad
  and tied, or one of the ops with their own rules, each total by it;
* it is lawful in its poison with memory: each valid core op that
  propagates poison propagates it with memory, from any memories, and
  returns a result on some defined operands;
* it is lawful in its monotonicity: each core op that runs by its own rule
  is monotone with memory at every layout and naming, at every width, valid
  or not.

_Every core function valid in the context of a module runs within that
module with memory_, wherever a run names the core's memories: it runs
within the module, and each core terminator is tied. Every core op that runs
by its own rule is monotone with memory at every width, valid or not. No
theorem below asks that the core lift the set monad: `alloca`, the loads
and stores, `fieldAddr`, `memCopy` and `memSet`, which have no tie and are
not terminators, join them with their own cases of monotonicity with memory
and their own totality.

The runs of a core function are its runs with memory at its module's
layout, where each memory of the core is the module's memory of the same
number: the runs that the modes report. The refinement of core functions and
the equivalence experiment of #282 are about them.

The three obligations of the section on fuel and progress hold of the runs
with memory of core functions, on every argument vector of their parameter
types, poison included, wherever a run names the core's memories:

* their runs with memory are fuel-monotone, for every function of every
  core module;
* every function of the tracer subset of a valid module, and every
  function without calls valid in its module, runs well, jumps and loops
  included. A function without calls runs only its own ops, so it needs
  only its own validity, by the theorems on progress with memory without
  calls;
* every function of a valid core module runs well, calls and recursion
  included.

On arguments that refine others, the runs with memory of every function of
every core module refine its runs with memory on those others, calls and
recursion included. Congruence in the callee needs no bound for the new
callee: every core op has finitely many outcomes (the section on congruence
in a core callee).

These are the core's guarantees, for the whole core dialect, `alloca`, the
loads and stores and `fieldAddr` included: the three lawful classes with memory and the lawful class of its
effects, progress and no stuck path, refined arguments, and congruence in
the callee from given memories. The statements without memory cover only
the code that touches none: the obligations of the core's ops over the set
monad cover the ops that touch no memory, and congruence with memory for a
callee that reaches no memory covers such callees. The theorems of the
lawful class over the set monad do not apply to the core at all. Each new
op that touches memory keeps every guarantee here holding, with its own
rule with memory and its own proofs, as `alloca` does. The human ruled
this on 2026-11-14, on #384
(`docs/decisions/semantics-m1-memory.md#the-cores-guarantees`).
-/

namespace Fir

/-- The core dialect is lawful in its totality: each core op that runs by
its own rule has an outcome from any memories, at every layout and naming:
each op that touches no memory from its own tie and its totality in the set
monad, and `alloca`, the loads and stores, `fieldAddr`, `memCopy` and `memSet` each by its own
rule. -/
instance Core.lawfulDialectTotal : LawfulDialectTotal CoreDialect :=
  ⟨fun op _ hc => Core.Op.memCases (P := fun op =>
      (isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none) →
        MemTotal (d := CoreDialect) op) op
    (fun op hm hi hc => MemTotal.ofLifts (Core.Op.liftsSetM op hm hi)
      (Core.Op.total_all op hc hm hi))
    (fun k t c a n _ => Core.alloca_memTotal k t c a n)
    (fun o w a n _ => Core.load_memTotal o w a n)
    (fun o w a n _ => Core.store_memTotal o w a n)
    (fun o mp a n _ => Core.loadPtr_memTotal o mp a n)
    (fun o mp a n _ => Core.storePtr_memTotal o mp a n)
    (fun o e m a n _ => Core.loadFloat_memTotal o e m a n)
    (fun o e m a n _ => Core.storeFloat_memTotal o e m a n)
    (fun s j n w _ => Core.fieldAddr_memTotal s j n w)
    (fun k o w n _ => Core.memCopy_memTotal k o w n)
    (fun o v w n _ => Core.memSet_memTotal o v w n) hc⟩

/-- The core dialect is lawful in its monotonicity: each core op that runs
by its own rule is monotone with memory, at every layout and naming: each op
that touches no memory from its own tie and its monotonicity in the set
monad, and `alloca`, the loads and stores, `fieldAddr`, `memCopy` and `memSet` each by its own
rule. -/
instance Core.lawfulDialectMonotone : LawfulDialectMonotone CoreDialect :=
  ⟨fun op _ hc => Core.Op.memCases (P := fun op =>
      (isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none) →
        MemMonotone (d := CoreDialect) op) op
    (fun op hm hi hc => MemMonotone.ofLifts (Core.Op.liftsSetM op hm hi)
      (Core.Op.monotone_all op hc))
    (fun k t c a n _ => Core.alloca_memMonotone k t c a n)
    (fun o w a n _ => Core.load_memMonotone o w a n)
    (fun o w a n _ => Core.store_memMonotone o w a n)
    (fun o mp a n _ => Core.loadPtr_memMonotone o mp a n)
    (fun o mp a n _ => Core.storePtr_memMonotone o mp a n)
    (fun o e m a n _ => Core.loadFloat_memMonotone o e m a n)
    (fun o e m a n _ => Core.storeFloat_memMonotone o e m a n)
    (fun s j n w _ => Core.fieldAddr_memMonotone s j n w)
    (fun k o w n _ => Core.memCopy_memMonotone k o w n)
    (fun o v w n _ => Core.memSet_memMonotone o v w n) hc⟩

/-- The core dialect is lawful in its poison with memory: each valid core op
instance that propagates poison propagates it with memory, and returns a
result on some defined operands, at every layout and naming: each op that
touches no memory from its own tie and its poison obligations in the set
monad, and `alloca`, the loads and stores, `fieldAddr`, `memCopy` and `memSet` each by its own
rule. -/
instance Core.lawfulDialectMemPoison : LawfulDialectMemPoison CoreDialect where
  poison_isRefinedBy _ := Core.Ty.poison_isRefinedBy
  propagates op _ hc := Core.Op.memCases (P := fun op =>
      poisonClass (d := CoreDialect) op = .propagates → MemPropagatesPoison (d := CoreDialect) op) op
    (fun op hm hi hc => MemPropagatesPoison.ofLifts (Core.Op.liftsSetM op hm hi)
      (Core.Op.propagates_all op hc))
    (fun k t c a n _ => Core.alloca_memPropagates k t c a n)
    (fun o w a n _ => Core.load_memPropagates o w a n)
    (fun o w a n _ => Core.store_memPropagates o w a n)
    (fun o mp a n _ => Core.loadPtr_memPropagates o mp a n)
    (fun o mp a n _ => Core.storePtr_memPropagates o mp a n)
    (fun o e m a n _ => Core.loadFloat_memPropagates o e m a n)
    (fun o e m a n _ => Core.storeFloat_memPropagates o e m a n)
    (fun s j n w _ => Core.fieldAddr_memPropagates s j n w)
    (fun k o w n _ => Core.memCopy_memPropagates k o w n)
    (fun o v w n _ => Core.memSet_memPropagates o v w n) hc
  returnsOnDefined op hv hc := Core.Op.memCases (P := fun op => TypesValid (d := CoreDialect) op →
      poisonClass (d := CoreDialect) op = .propagates → MemReturnsOnDefined (d := CoreDialect) op) op
    (fun op hm hi hv hc => MemReturnsOnDefined.ofLifts (Core.Op.liftsSetM op hm hi)
      (Core.Op.returnsOnDefined_valid op hm hi hv hc))
    (fun k t c a n _ _ => Core.alloca_memReturnsOnDefined k t c a n)
    (fun o w a n _ _ => Core.load_memReturnsOnDefined o w a n)
    (fun o w a n _ _ => Core.store_memReturnsOnDefined o w a n)
    (fun o mp a n _ _ => Core.loadPtr_memReturnsOnDefined o mp a n)
    (fun o mp a n _ _ => Core.storePtr_memReturnsOnDefined o mp a n)
    (fun o e m a n _ _ => Core.loadFloat_memReturnsOnDefined o e m a n)
    (fun o e m a n _ _ => Core.storeFloat_memReturnsOnDefined o e m a n)
    (fun s j n w _ _ => Core.fieldAddr_memReturnsOnDefined s j n w)
    (fun k o w n _ _ => Core.memCopy_memReturnsOnDefined k o w n)
    (fun o v w n _ _ => Core.memSet_memReturnsOnDefined o v w n) hv hc

namespace Core

variable {M : Module CoreDialect} {f : Func CoreDialect} {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N) (L : RunItems)

/-- The runs of the function `f` of the core module `M`: its runs with memory
at the module's layout, where the core's memory `x` is the module's memory
`x` and each op is given the items of the module's own table, on each
argument vector of its parameter types, poison included, at each budget.
They are the runs that the modes report. -/
def funcRuns (M : Module CoreDialect) (f : Func CoreDialect) : FuncRuns (f.params.map (·.2)) :=
  f.memRuns M.layout.entry id M.runItems M

/-- Every core terminator is tied: it touches no memory. -/
theorem Op.liftsSetM_of_terminator {op : Op} (h : Fir.isTerminator (d := CoreDialect) op = true) :
    OpLiftsSetM (d := CoreDialect) op :=
  Op.liftsSetM op (by cases op <;> first | rfl | cases h) (by cases op <;> first | rfl | cases h)

/-- Every core terminator and every core op with no callee is monotone with
memory, at every width, layout and naming: every core op but `call`. Each
tied op is monotone in the set monad, and `alloca`, the loads and stores,
`fieldAddr`, `memCopy` and `memSet` are monotone by their own rules. -/
theorem Op.memMonotone_all (op : Op)
    (h : Fir.isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none) :
    MemMonotone (d := CoreDialect) op :=
  Op.memCases (P := fun op => (Fir.isTerminator (d := CoreDialect) op = true ∨
      callee? (d := CoreDialect) op = none) → MemMonotone (d := CoreDialect) op) op
    (fun op hm hi h => MemMonotone.ofLifts (Op.liftsSetM op hm hi) (Op.monotone_all op h))
    (fun k t c a n _ => alloca_memMonotone k t c a n)
    (fun o w a n _ => load_memMonotone o w a n)
    (fun o w a n _ => store_memMonotone o w a n)
    (fun o mp a n _ => loadPtr_memMonotone o mp a n)
    (fun o mp a n _ => storePtr_memMonotone o mp a n)
    (fun o e m a n _ => loadFloat_memMonotone o e m a n)
    (fun o e m a n _ => storeFloat_memMonotone o e m a n)
    (fun s j n w _ => fieldAddr_memMonotone s j n w)
    (fun k o w n _ => memCopy_memMonotone k o w n)
    (fun o v w n _ => memSet_memMonotone o v w n) h

/-- A core function that runs within a module runs within it with memory,
wherever a run names the core's memories: each of its terminators is tied. -/
theorem inModuleAt_of_inModule (h : f.InModule M) : f.InModuleAt lay ρ L M :=
  h.inModuleAt_of_tied lay ρ L fun _ _ _ _ hT => Op.liftsSetM_of_terminator hT

/-- A core function valid in the context of a module runs within that
module with memory, wherever a run names the core's memories. -/
theorem inModuleAt_of_valid (hv : f.Valid M.context) : f.InModuleAt lay ρ L M :=
  inModuleAt_of_inModule lay ρ L (inModule_of_valid hv)

/-! # Fuel and progress -/

/-- More fuel never changes how a run with memory of a function of a core
module returns or hits UB, wherever a run names the core's memories, calls
and recursion included. -/
theorem fuelMonotone (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ L M args) :=
  Func.memRuns_fuelMonotone lay ρ L M f args

/-- No path of a run with memory of a function of a valid core module is
stuck, calls and recursion included, wherever a run names the core's
memories. -/
theorem neverStuck (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ L M args) :=
  Func.memNeverStuck lay ρ L hM.funcs (fun _ hg => inModuleAt_of_valid lay ρ L (hM.funcs _ hg)) hf
    args

/-- A run with memory of a function of a valid core module has an outcome
at every budget, calls and recursion included, wherever a run names the
core's memories. -/
theorem progress (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ L M args) :=
  Func.memProgress lay ρ L hM.funcs (fun _ hg => inModuleAt_of_valid lay ρ L (hM.funcs _ hg)) hf
    args

/-- Every function of a valid core module runs well with memory on every
argument vector, calls and recursion included, wherever a run names the
core's memories. -/
theorem runsWell (hM : M.Valid) (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    RunsWell (f.memRuns lay ρ L M args) :=
  ⟨fuelMonotone lay ρ L M f args, progress lay ρ L hM hf args, neverStuck lay ρ L hM hf args⟩

/-- A core function that runs within itself and is valid in its module runs
well with memory on every argument vector, jumps and loops included,
wherever a run names the core's memories. -/
theorem runsWell_of_local (hv : f.Valid M.context) (hl : f.Local)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (f.memRuns lay ρ L M args) :=
  have hm := inModuleAt_of_inModule lay ρ L (hl.inModule M)
  ⟨fuelMonotone lay ρ L M f args, Func.memProgress_of_local lay ρ L hv hl.noCall hm args,
    Func.memNeverStuck_of_local lay ρ L hv hl.noCall hm args⟩

/-- A function without calls that is valid in its module runs well with
memory on every argument vector, jumps and loops included, wherever a run
names the core's memories. -/
theorem callFree_runsWell (hv : f.Valid M.context) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (f.memRuns lay ρ L M args) :=
  runsWell_of_local lay ρ L hv (local_of_valid hv hc) args

/-- More fuel never changes how a run with memory of a valid core function
without calls returns or hits UB. -/
theorem callFree_fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ L M args) :=
  (callFree_runsWell lay ρ L (hM.funcs f hf) hc args).fuelMonotone

/-- A run with memory of a valid core function without calls has an outcome
at every budget. -/
theorem callFree_progress (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ L M args) :=
  (callFree_runsWell lay ρ L (hM.funcs f hf) hc args).progress

/-- No path of a run with memory of a valid core function without calls is
stuck. -/
theorem callFree_neverStuck (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ L M args) :=
  (callFree_runsWell lay ρ L (hM.funcs f hf) hc args).neverStuck

/-- Every function of the tracer subset in a valid core module runs well
with memory on every argument vector, wherever a run names the core's
memories. -/
theorem tracer_runsWell (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (f.memRuns lay ρ L M args) :=
  runsWell_of_local lay ρ L (hM.funcs f hf) (straight_of_tracer (hM.funcs f hf) ht).local args

/-- More fuel never changes how a run with memory of a valid function of
the tracer subset returns or hits UB. -/
theorem tracer_fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ L M args) :=
  (tracer_runsWell lay ρ L hM hf ht args).fuelMonotone

/-- A run with memory of a valid function of the tracer subset has an
outcome at every budget. -/
theorem tracer_progress (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ L M args) :=
  (tracer_runsWell lay ρ L hM hf ht args).progress

/-- No path of a run with memory of a valid function of the tracer subset
is stuck. -/
theorem tracer_neverStuck (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ L M args) :=
  (tracer_runsWell lay ρ L hM hf ht args).neverStuck

/-! # Refinement -/

/-- Refined arguments, with memory: on arguments that refine others, a
poison by any value, the runs with memory of every function of every core
module refine its runs with memory on those others, calls and recursion
included, wherever a run names the core's memories. -/
theorem args_isRefinedBy (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ L M a) ⊑ observable (f.memRuns lay ρ L M a') :=
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
  have hm : ∀ g : Func CoreDialect, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => Op.memMonotone_all o.op hc lay ρ L
  Func.memRuns_isRefinedBy_of_from lay ρ L (Func.memRunsFrom_args_isRefinedBy M (fun g _ => hm g) f
    (hm f) h (Memory.Memories.isRefinedBy_refl _))

end Core

end Fir
