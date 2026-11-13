import Fir.Core.EffectLaws
import Fir.Core.CallRefine
import Fir.Execution.MemoryLocal
import Fir.Execution.MemoryReplace
import Fir.Execution.MemoryPoison

/-!
# Every valid core function, with memory

The core dialect's ops touch no memory: each runs with memory by its rule
in the set monad and keeps the memories, so each core op is tied (the
section on the core's rules with memory). So its obligations with memory
follow op by op, each from the op's own tie and what the op meets in the
set monad:

* _the core dialect is lawful in its totality_: each core terminator and
  each core op with no callee, total in the set monad, is total with
  memory;
* it is lawful in its poison with memory: each valid core op that
  propagates poison propagates it with memory, from any memories, and
  returns a result on some defined operands;
* it is lawful in its monotonicity: each core op that runs by its own rule
  is monotone in the set monad at every width, valid or not, so it is
  monotone with memory at every layout and naming.

Since every op is tied, the core dialect lifts the set monad: that is a
theorem here, not its definition.

_Every core function valid in the context of a module runs within that
module with memory_, wherever a run names the core's memories: it runs
within the module, and each core terminator is tied. Every core op that runs
by its own rule is monotone with memory at every width, valid or not. No
theorem below asks that the core lift the set monad: an op that touches
memory, which is not a terminator, joins them with its own case of
monotonicity with memory and its own totality.

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
recursion included. Congruence in the callee holds with memory when the new
callee's runs from given memories refine the old one's and are bounded:
a call starts from its caller's memories, so finitely many argument vectors
do not bound them.
-/

namespace Fir

/-- The core dialect is lawful in its totality: each core op that runs by
its own rule has an outcome from any memories, at every layout and naming,
from its own tie and its totality in the set monad. -/
instance Core.lawfulDialectTotal : LawfulDialectTotal CoreDialect :=
  ⟨fun op hv hc => MemTotal.ofLifts (Core.Op.liftsSetM op) (LawfulDialectPoison.total op hv hc)⟩

/-- The core dialect is lawful in its monotonicity: each core op that runs
by its own rule is monotone with memory, at every layout and naming, from
its own tie and its monotonicity in the set monad. -/
instance Core.lawfulDialectMonotone : LawfulDialectMonotone CoreDialect :=
  ⟨fun op hv hc =>
    MemMonotone.ofLifts (Core.Op.liftsSetM op) (LawfulDialectPoison.monotone op hv hc)⟩

/-- The core dialect is lawful in its poison with memory: each valid core op
instance that propagates poison propagates it with memory, and returns a
result on some defined operands, at every layout and naming, from its own
tie and its poison obligations in the set monad. -/
instance Core.lawfulDialectMemPoison : LawfulDialectMemPoison CoreDialect where
  poison_isRefinedBy := LawfulDialectPoison.poison_isRefinedBy
  propagates op hv hc :=
    MemPropagatesPoison.ofLifts (Core.Op.liftsSetM op) (LawfulDialectPoison.propagates op hv hc)
  returnsOnDefined op hv hc :=
    MemReturnsOnDefined.ofLifts (Core.Op.liftsSetM op)
      (LawfulDialectPoison.returnsOnDefined op hv hc)

/-- The core dialect's semantics with memory lifts its semantics in the set
monad: every core op is tied. It is proved from each op's tie. No theorem on
the core's runs, no test of a dialect over the core and no equivalence test
uses it. It stays until the human rules on congruence in the callee
([#373](https://github.com/pmatos/funk/issues/373)), whose form over finitely
many argument vectors is stated over the runs in the set monad. -/
instance Core.liftsSetM : LiftsSetM CoreDialect := LiftsSetM.ofOpLifts Core.Op.liftsSetM

namespace Core

variable {M : Module CoreDialect} {f : Func CoreDialect} {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N)

/-- The runs of the function `f` of the core module `M`: its runs with memory
at the module's layout, where the core's memory `x` is the module's memory
`x`, on each argument vector of its parameter types, poison included, at
each budget. They are the runs that the modes report. -/
def funcRuns (M : Module CoreDialect) (f : Func CoreDialect) : FuncRuns (f.params.map (·.2)) :=
  f.memRuns M.layout.entry id M

/-- Every core terminator is tied: it touches no memory. -/
theorem Op.liftsSetM_of_terminator {op : Op} (_ : Fir.isTerminator (d := CoreDialect) op = true) :
    OpLiftsSetM (d := CoreDialect) op :=
  Op.liftsSetM op

/-- Every core terminator and every core op with no callee is monotone with
memory, at every width, layout and naming: every core op but `call`. Each op
that touches no memory is monotone in the set monad and tied. -/
theorem Op.memMonotone_all (op : Op)
    (h : Fir.isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none) :
    MemMonotone (d := CoreDialect) op :=
  MemMonotone.ofLifts (Op.liftsSetM op) (Op.monotone_all op h)

/-- A core function that runs within a module runs within it with memory,
wherever a run names the core's memories: each of its terminators is tied. -/
theorem inModuleAt_of_inModule (h : f.InModule M) : f.InModuleAt lay ρ M :=
  h.inModuleAt_of_tied lay ρ fun _ _ _ _ hT => Op.liftsSetM_of_terminator hT

/-- A core function valid in the context of a module runs within that
module with memory, wherever a run names the core's memories. -/
theorem inModuleAt_of_valid (hv : f.Valid M.context) : f.InModuleAt lay ρ M :=
  inModuleAt_of_inModule lay ρ (inModule_of_valid hv)

/-! # Fuel and progress -/

/-- More fuel never changes how a run with memory of a function of a core
module returns or hits UB, wherever a run names the core's memories, calls
and recursion included. -/
theorem fuelMonotone (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ M args) :=
  Func.memRuns_fuelMonotone lay ρ M f args

/-- No path of a run with memory of a function of a valid core module is
stuck, calls and recursion included, wherever a run names the core's
memories. -/
theorem neverStuck (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ M args) :=
  Func.memNeverStuck lay ρ hM.funcs (fun _ hg => inModuleAt_of_valid lay ρ (hM.funcs _ hg)) hf
    args

/-- A run with memory of a function of a valid core module has an outcome
at every budget, calls and recursion included, wherever a run names the
core's memories. -/
theorem progress (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ M args) :=
  Func.memProgress lay ρ hM.funcs (fun _ hg => inModuleAt_of_valid lay ρ (hM.funcs _ hg)) hf
    args

/-- Every function of a valid core module runs well with memory on every
argument vector, calls and recursion included, wherever a run names the
core's memories. -/
theorem runsWell (hM : M.Valid) (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    RunsWell (f.memRuns lay ρ M args) :=
  ⟨fuelMonotone lay ρ M f args, progress lay ρ hM hf args, neverStuck lay ρ hM hf args⟩

/-- A core function that runs within itself and is valid in its module runs
well with memory on every argument vector, jumps and loops included,
wherever a run names the core's memories. -/
theorem runsWell_of_local (hv : f.Valid M.context) (hl : f.Local)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (f.memRuns lay ρ M args) :=
  have hm := inModuleAt_of_inModule lay ρ (hl.inModule M)
  ⟨fuelMonotone lay ρ M f args, Func.memProgress_of_local lay ρ hv hl.noCall hm args,
    Func.memNeverStuck_of_local lay ρ hv hl.noCall hm args⟩

/-- A function without calls that is valid in its module runs well with
memory on every argument vector, jumps and loops included, wherever a run
names the core's memories. -/
theorem callFree_runsWell (hv : f.Valid M.context) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (f.memRuns lay ρ M args) :=
  runsWell_of_local lay ρ hv (local_of_valid hv hc) args

/-- More fuel never changes how a run with memory of a valid core function
without calls returns or hits UB. -/
theorem callFree_fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ M args) :=
  (callFree_runsWell lay ρ (hM.funcs f hf) hc args).fuelMonotone

/-- A run with memory of a valid core function without calls has an outcome
at every budget. -/
theorem callFree_progress (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ M args) :=
  (callFree_runsWell lay ρ (hM.funcs f hf) hc args).progress

/-- No path of a run with memory of a valid core function without calls is
stuck. -/
theorem callFree_neverStuck (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ M args) :=
  (callFree_runsWell lay ρ (hM.funcs f hf) hc args).neverStuck

/-- Every function of the tracer subset in a valid core module runs well
with memory on every argument vector, wherever a run names the core's
memories. -/
theorem tracer_runsWell (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (f.memRuns lay ρ M args) :=
  runsWell_of_local lay ρ (hM.funcs f hf) (straight_of_tracer (hM.funcs f hf) ht).local args

/-- More fuel never changes how a run with memory of a valid function of
the tracer subset returns or hits UB. -/
theorem tracer_fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.memRuns lay ρ M args) :=
  (tracer_runsWell lay ρ hM hf ht args).fuelMonotone

/-- A run with memory of a valid function of the tracer subset has an
outcome at every budget. -/
theorem tracer_progress (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ M args) :=
  (tracer_runsWell lay ρ hM hf ht args).progress

/-- No path of a run with memory of a valid function of the tracer subset
is stuck. -/
theorem tracer_neverStuck (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ M args) :=
  (tracer_runsWell lay ρ hM hf ht args).neverStuck

/-! # Refinement -/

/-- Refined arguments, with memory: on arguments that refine others, a
poison by any value, the runs with memory of every function of every core
module refine its runs with memory on those others, calls and recursion
included, wherever a run names the core's memories. -/
theorem args_isRefinedBy (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ M a) ⊑ observable (f.memRuns lay ρ M a') :=
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  have hm : ∀ g : Func CoreDialect, g.MemOpsMonotone N (unitsOf lay) :=
    fun _ _ _ o _ hc => Op.memMonotone_all o.op hc lay ρ
  Func.memRuns_isRefinedBy_of_from lay ρ (Func.memRunsFrom_args_isRefinedBy M (fun g _ => hm g) f
    (hm f) h (Memory.Memories.isRefinedBy_refl _))

/-- Congruence in the callee, with memory: replacing the body of a function
`@g` of a valid core module with one under which `@g`, run in the new module
from given memories, refines `@g` in the old, and whose runs from given
memories are bounded, refines every function of the module with memory,
calls and recursion included, wherever a run names the core's memories. -/
theorem memReplaceBody_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (b : Region CoreDialect)
    (hbound : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_bound lay ρ Ty.isRefinedBy_refl Ty.isRefinedBy_trans
    hM hg b hbound h hf).2

/-- Every function of the module other than `@g`, a caller of it or not,
is refined with memory by itself in the module with `@g`'s new body, under
the hypotheses of congruence in the callee with memory. -/
theorem memCaller_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (b : Region CoreDialect)
    (hbound : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ M ⊑ f.memRuns lay ρ (M.replaceBody g.name b) := by
  have := memReplaceBody_isRefinedBy lay ρ hM hg b hbound h hf
  change f.memRuns lay ρ M ⊑
    Func.memRuns lay ρ _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

end Core

end Fir
