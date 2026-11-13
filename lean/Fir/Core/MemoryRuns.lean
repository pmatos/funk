import Fir.Core.EffectLaws
import Fir.Core.CallRefine
import Fir.Execution.MemoryProgress
import Fir.Execution.MemoryReplace
import Fir.Execution.MemoryPoison

/-!
# Every valid core function, with memory

The core dialect's ops touch no memory: its semantics with memory runs each
op by its rule in the set monad and keeps the memories (the section on the
core's effects). So its two obligations for progress with memory follow
from what it already meets in the set monad:

* _the core dialect is lawful in its totality_: it is lawful, and it lifts
  the set monad, so each core terminator and each core op with no callee,
  total in the set monad, is total with memory;
* _every core function valid in the context of a module runs within that
  module with memory_, wherever a run names the core's memories: it runs
  within the module, and the core lifts the set monad.

So no path of a run with memory of a function of a valid core module is
stuck, and it has an outcome at every budget, calls and recursion included,
wherever a run names the core's memories.

The core dialect is also lawful in its poison with memory and in its
monotonicity, since it is lawful and lifts the set monad: each valid core
op that propagates poison propagates it with memory, from any memories,
and returns a result on some defined operands. Each core op that runs by
its own rule is monotone in the set monad at every width, valid or not, so
it is monotone with memory at every naming: on arguments that refine
others, the runs with memory of every function of every core module refine
its runs with memory on those others, calls and recursion included.
-/

namespace Fir

/-- The core dialect is lawful in its totality: each core op that runs by
its own rule has an outcome from any memories, at every naming. -/
instance Core.lawfulDialectTotal : LawfulDialectTotal CoreDialect := LawfulDialectTotal.ofLawful

/-- The core dialect is lawful in its monotonicity: each core op that runs
by its own rule is monotone with memory, at every naming. -/
instance Core.lawfulDialectMonotone : LawfulDialectMonotone CoreDialect :=
  LawfulDialectMonotone.ofLawful

/-- The core dialect is lawful in its poison with memory: each valid core op
instance that propagates poison propagates it with memory, and returns a
result on some defined operands, at every naming. -/
instance Core.lawfulDialectMemPoison : LawfulDialectMemPoison CoreDialect :=
  LawfulDialectMemPoison.ofLawful

namespace Core

variable {M : Module CoreDialect} {f : Func CoreDialect} {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem CoreDialect → N)

/-- No path of a run with memory of a function of a valid core module is
stuck, calls and recursion included, wherever a run names the core's
memories. -/
theorem memNeverStuck (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns lay ρ M args) :=
  Func.memNeverStuck lay ρ hM.funcs
    (fun _ hg => (inModule_of_valid (hM.funcs _ hg)).inModuleAt lay ρ) hf args

/-- A run with memory of a function of a valid core module has an outcome
at every budget, calls and recursion included, wherever a run names the
core's memories. -/
theorem memProgress (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns lay ρ M args) :=
  Func.memProgress lay ρ hM.funcs
    (fun _ hg => (inModule_of_valid (hM.funcs _ hg)).inModuleAt lay ρ) hf args

/-- Refined arguments, with memory: on arguments that refine others, a
poison by any value, the runs with memory of every function of every core
module refine its runs with memory on those others, calls and recursion
included, wherever a run names the core's memories. -/
theorem memRuns_args_isRefinedBy (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns lay ρ M a) ⊑ observable (f.memRuns lay ρ M a') :=
  letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
  have hm : ∀ g : Func CoreDialect, g.MemOpsMonotone N (unitsOf lay) :=
    fun g b hb o ho hc => MemMonotone.ofLifts (opsMonotone_all g b hb o ho hc) lay ρ
  Func.memRuns_isRefinedBy_of_from lay ρ (Func.memRunsFrom_args_isRefinedBy M (fun g _ => hm g) f
    (hm f) h (Memory.Memories.isRefinedBy_refl _))

end Core

end Fir
