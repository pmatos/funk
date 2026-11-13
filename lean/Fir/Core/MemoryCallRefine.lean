import Fir.Core.MemoryRuns
import Fir.Execution.MemoryFreeReplace

/-!
# Congruence in a core callee that touches no memory

Congruence in the callee for the core dialect is stated over the runs with
memory of its functions, wherever a run names the core's memories. It
takes two forms (ADR-2026-11-09-1542; the human's ruling on #373 of
2026-11-13, `docs/decisions/semantics-refinement.md#refinement-with-memory`):

* for a callee `@g` with no pointer parameter, whose effects include no
  memory read, write or allocation, it asks for no budget: finitely many
  argument vectors bound the runs of a callee that touches no memory. This
  section states it;
* for a callee that touches memory, it asks for one budget past which no
  run of the new `@g` from any memories runs out of fuel unless it diverges
  (`Core.memReplaceBody_isRefinedBy`, the section on core functions with
  memory), until [#214](https://github.com/pmatos/funk/issues/214).

A callee touches no memory when its summary, in the module where it runs,
touches none. The core dialect meets what the general theorems ask:

* each core op ignores the memories, since none touches memory: each runs
  by its rule in the set monad and keeps the memories. An op that touches
  memory declares it, so only the ops that declare no memory effect are
  asked;
* no core op declares a memory effect, so the summary of a function of a
  core module whose calls each name one of its functions touches no memory;
* the refinement of core values is reflexive and transitive, the symbols of
  a valid module are unique, and an integer or float type has finitely many
  values (the section on refinement through core calls).

Replacing the body of such a `@g` of a valid core module, with one under
which `@g`, run in the new module, refines `@g` in the old, and under which
its summary in the new module touches no memory, refines every function of
the module with memory. The hypothesis is stated with memory when the old
`@g` touches no memory either, as it was over the runs in the set monad, and
from given memories otherwise. A function other than `@g`, a caller of it or
not, is refined by itself in the new module.

As over the runs in the set monad, congruence asks nothing of the new body
but that, and compares real behaviours when the new function is valid in
the old module's context: then the new module is valid, and no run of
either module has a stuck path (the section on core functions with memory).
-/

namespace Fir.Core

/-- No core op declares a memory effect. -/
theorem Op.effects_touchesNoMemory (op : Op) :
    (Fir.effects (d := CoreDialect) op).TouchesNoMemory := fun _ => by
  cases op <;> exact ⟨nofun, nofun, nofun⟩

/-- The summary of every function of a core table whose calls each name a
function of the table touches no memory. -/
theorem summary_touchesNoMemory {t : SymbolTable CoreDialect}
    (hcalls : ∀ f ∈ t.funcs, ∀ o ∈ f.allOps, o.call?.all fun c => (t.func? c).isSome)
    (s : Name) : (t.summary s).TouchesNoMemory :=
  SymbolTable.summary_touchesNoMemory (fun _ _ _ o _ => Op.effects_touchesNoMemory o.op)
    (fun _ _ hf o ho c hc => by
      have := hcalls _ (List.mem_of_find?_eq_some hf) o ho
      rw [hc] at this
      simpa using this) s

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
and under which its summary in the new module touches no memory, refines
every function of the module with memory, calls and recursion included,
wherever a run names the core's memories. -/
theorem replaceBody_isRefinedBy_of_from (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (hfin : ∀ t ∈ g.params.map (·.2), t.Finite) (b : Region CoreDialect)
    (hmem : ((M.replaceBody g.name b).table.summary g.name).TouchesNoMemory)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_finite lay ρ Ty.isRefinedBy_refl Ty.isRefinedBy_trans
    (opsIgnoreMemory lay ρ) hM hg b ⟨argVectors _ hfin, mem_argVectors hfin⟩ hmem h hf).2

/-- Congruence in the callee, with memory: replacing the body of a function
`@g` with no pointer parameter of a valid core module, whose summary touches
no memory, with one under which `@g`, run with memory in the new module,
refines `@g` in the old, and under which its summary in the new module
touches no memory, refines every function of the module with memory, calls
and recursion included, wherever a run names the core's memories. -/
theorem replaceBody_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (hfin : ∀ t ∈ g.params.map (·.2), t.Finite) (b : Region CoreDialect)
    (hold : (M.table.summary g.name).TouchesNoMemory)
    (hmem : ((M.replaceBody g.name b).table.summary g.name).TouchesNoMemory)
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
    (hold : (M.table.summary g.name).TouchesNoMemory)
    (hmem : ((M.replaceBody g.name b).table.summary g.name).TouchesNoMemory)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ M ⊑ f.memRuns lay ρ (M.replaceBody g.name b) := by
  have := replaceBody_isRefinedBy lay ρ hM hg hfin b hold hmem h hf
  change f.memRuns lay ρ M ⊑
    Func.memRuns lay ρ _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

end Fir.Core
