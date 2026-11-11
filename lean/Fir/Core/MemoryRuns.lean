import Fir.Core.EffectLaws
import Fir.Execution.MemoryProgress

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
-/

namespace Fir

/-- The core dialect is lawful in its totality: each core op that runs by
its own rule has an outcome from any memories, at every naming. -/
instance Core.lawfulDialectTotal : LawfulDialectTotal CoreDialect := LawfulDialectTotal.ofLawful

namespace Core

variable {M : Module CoreDialect} {f : Func CoreDialect} {N : Type} [DecidableEq N]
  (unit : N → Nat) (ρ : DialectEffects.Mem CoreDialect → N)

/-- No path of a run with memory of a function of a valid core module is
stuck, calls and recursion included, wherever a run names the core's
memories. -/
theorem memNeverStuck (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (f.memRuns unit ρ M args) :=
  Func.memNeverStuck unit ρ hM.funcs
    (fun _ hg => (inModule_of_valid (hM.funcs _ hg)).inModuleAt unit ρ) hf args

/-- A run with memory of a function of a valid core module has an outcome
at every budget, calls and recursion included, wherever a run names the
core's memories. -/
theorem memProgress (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (f.memRuns unit ρ M args) :=
  Func.memProgress unit ρ hM.funcs
    (fun _ hg => (inModule_of_valid (hM.funcs _ hg)).inModuleAt unit ρ) hf args

end Core

end Fir
