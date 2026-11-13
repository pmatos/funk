import Fir.Core.MemoryRuns
import Fir.Execution.MemoryFreeReplace

/-!
# Congruence in a core callee that touches no memory

Congruence in the callee for the core dialect is stated over the runs with
memory of its functions, wherever a run names the core's memories. By the
human's ruling on #373 of 2026-11-13
(`docs/decisions/semantics-refinement.md#refinement-with-memory`), it takes
two forms:

* for a callee `@g` with no pointer parameter, whose effects include no
  memory read, write or allocation, it asks for no budget: finitely many
  argument vectors bound the runs of a callee that touches no memory. This
  section states it;
* for a callee that touches memory, it asks for one budget past which no
  run of the new `@g` from any memories runs out of fuel unless it diverges
  (`Core.memReplaceBody_isRefinedBy`, the section on core functions with
  memory), until [#214](https://github.com/pmatos/funk/issues/214).

A callee touches no memory when it reaches no memory in the module where it
runs: no function that its run may reach declares a memory effect. The core
dialect meets what the general theorems ask:

* no core op declares a memory effect, so every function of every core
  module reaches no memory;
* each core op ignores the memories, since none touches memory: each runs
  by its rule in the set monad and keeps the memories. An op that touches
  memory declares it, so only the ops that declare no memory effect are
  asked;
* the core dialect is lawful in its monotonicity, the refinement of core
  values is reflexive and transitive, the symbols of a valid module are
  unique, and an integer or float type has finitely many values (the
  section on refinement through core calls).

Replacing the body of such a `@g` of a valid core module, with one under
which `@g`, run in the new module, refines `@g` in the old, and under which
it reaches no memory in the new module, refines every function of the
module with memory. The hypothesis is stated with memory when the old `@g`
reaches no memory either, as it was over the runs in the set monad, and
from given memories otherwise. A function other than `@g`, a caller of it or
not, is refined by itself in the new module. Since every core function
reaches no memory, these hypotheses hold of every core callee today; they
are stated so that a callee that touches memory, once a core op does, is
left to the form with the budget.

Congruence goes through the lawful class, which covers the functions of
valid modules, so it asks for a valid module. As over the runs in the set
monad, it asks nothing of the new body but that, and compares real
behaviours when the new function is valid in the old module's context: then
the new module is valid, and no run of either module has a stuck path (the
section on core functions with memory).
-/

namespace Fir.Core

/-- No core op declares a memory effect. -/
theorem Op.effects_touchesNoMemory (op : Op) :
    (Fir.effects (d := CoreDialect) op).TouchesNoMemory := fun _ => by
  cases op <;> exact ⟨nofun, nofun, nofun⟩

/-- Every function of every core table reaches no memory: no core op
declares a memory effect. -/
theorem reachesNoMemory (t : SymbolTable CoreDialect) (s : Name) : t.ReachesNoMemory s :=
  fun _ _ _ _ o _ => Op.effects_touchesNoMemory o.op

variable {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem CoreDialect → N)

/-- Each core op ignores the memories where it declares no memory effect,
at every layout and naming: it runs by its rule in the set monad and keeps
the memories. -/
theorem opsIgnoreMemory :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    OpsIgnoreMemory CoreDialect N (unitsOf lay) := fun op _ _ =>
  OwnRuleHas.ofLifts (Op.liftsSetM op) lay ρ (P := IgnoresMemory) IgnoresMemory.lift

variable {M : Module CoreDialect} {f : Func CoreDialect}

/-- Congruence in the callee, with memory: replacing the body of a function
`@g` with no pointer parameter of a valid core module, with one under which
`@g`, run in the new module from given memories, refines `@g` in the old,
and under which it reaches no memory in the new module, refines
every function of the module with memory, calls and recursion included,
wherever a run names the core's memories. -/
theorem replaceBody_isRefinedBy_of_from (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (hfin : ∀ t ∈ g.params.map (·.2), t.Finite) (b : Region CoreDialect)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_finite lay ρ Ty.isRefinedBy_refl Ty.isRefinedBy_trans
    (opsIgnoreMemory lay ρ) hM hg b ⟨argVectors _ hfin, mem_argVectors hfin⟩ hmem h hf).2

/-- Congruence in the callee, with memory: replacing the body of a function
`@g` with no pointer parameter of a valid core module, which reaches no
memory, with one under which `@g`, run with memory in the new module,
refines `@g` in the old, and under which it reaches no memory in the new
module, refines every function of the module with memory, calls
and recursion included, wherever a run names the core's memories. -/
theorem replaceBody_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (hfin : ∀ t ∈ g.params.map (·.2), t.Finite) (b : Region CoreDialect)
    (hold : M.table.ReachesNoMemory g.name)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  Func.memRuns_replaceBody_isRefinedBy_of_memRuns lay ρ Ty.isRefinedBy_refl Ty.isRefinedBy_trans
    (opsIgnoreMemory lay ρ) hM hg b ⟨argVectors _ hfin, mem_argVectors hfin⟩ hold hmem h hf

/-- Every function of the module other than `@g`, a caller of it or not,
is refined with memory by itself in the module with `@g`'s new body, under
the hypotheses of congruence in the callee for a callee that touches no
memory. -/
theorem caller_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (hfin : ∀ t ∈ g.params.map (·.2), t.Finite) (b : Region CoreDialect)
    (hold : M.table.ReachesNoMemory g.name)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ M ⊑ f.memRuns lay ρ (M.replaceBody g.name b) := by
  have := replaceBody_isRefinedBy lay ρ hM hg hfin b hold hmem h hf
  change f.memRuns lay ρ M ⊑
    Func.memRuns lay ρ _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

end Fir.Core
