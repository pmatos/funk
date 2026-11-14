import Fir.Core.MemoryRuns
import Fir.Core.TreeRules
import Fir.Execution.MemoryFreeReplace
import Fir.Execution.MemoryFiniteReplace

/-!
# Congruence in a core callee

Congruence in the callee for the core dialect is stated over the runs with
memory of its functions, wherever a run names the core's memories. It asks
for no budget for the new callee, in two forms:

* from given memories, for every callee `@g`, whatever its parameter types,
  pointers included, and whatever its new body does to the memories. Every
  core op has finitely many outcomes with memory: each runs by its rule in
  the set monad and keeps the memories, and its rule in the set monad is
  the set of its rule in the tree of choices, whose choices of _w_ bits have
  2 to the power _w_ options. So congruence with ops of finitely many
  outcomes applies (#214,
  `docs/decisions/semantics-refinement.md#congruence-in-the-callee`). No core
  op touches memory yet; one that does, such as an allocation, has no tie,
  and must show by its own rule that it has finitely many outcomes, which a
  deterministic allocation has;
* with memory, for a callee that reaches no memory in the module where it
  runs, nor in the new one: no function that its run may reach declares a
  memory effect. Its runs then do not depend on the memories, so refinement
  with memory, from the empty memories, is refinement from given memories,
  and the form from given memories applies. Like it, this form asks nothing
  of the parameter types of `@g`, pointers included (#214). Before #214 it
  asked that `@g` have no pointer parameter, as the human's ruling on #373
  of 2026-11-13 set it
  (`docs/decisions/semantics-refinement.md#refinement-with-memory`).

The core dialect meets what the general theorems ask:

* no core op declares a memory effect, so every function of every core
  module reaches no memory today. The form with memory still asks it of
  `@g`, so that it does not depend on every core function reaching none;
* each core op ignores the memories, since none touches memory. An op that
  touches memory declares it, so only the ops that declare no memory effect
  are asked;
* the core dialect is lawful in its monotonicity, the refinement of core
  values is reflexive and transitive, and the symbols of a valid module are
  unique.

A function other than `@g`, a caller of it or not, is refined by itself in
the new module. Congruence goes through the lawful class, which covers the
functions of valid modules, so it asks for a valid module. As over the runs
in the set monad, it asks nothing of the new body but that, and compares
real behaviours when the new function is valid in the old module's
context: then the new module is valid, and no run of either module has a
stuck path (the section on core functions with memory).
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

/-- Each core op that runs by its own rule has finitely many outcomes with
memory, at every layout and naming: it runs by its rule in the set monad and
keeps the memories, and its rule in the set monad is the set of its rule in
the tree of choices, whose choices of bits have finitely many options. -/
theorem opsFinite :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    OpsFinite CoreDialect N (unitsOf lay) := fun op _ args => by
  have hm := denoteIn_mapsDenote (ChoiceTree.toSetMorphism (ε := Op)) ChoiceTree.toSet_keeps
    (fun op => .noOutcome op) (fun _ _ => False) fun _ => rfl
  rw [(Op.liftsSetM op lay ρ args).1, (Op.liftsSetM op lay ρ args).2]
  refine ⟨fun _ => FinitelyMany.lift ?_, fun _ => FinitelyMany.lift ?_⟩
  · rw [← hm.denote op args]
    exact ChoiceTree.toSet_finitelyMany _
  · rw [← hm.exit op args]
    exact ChoiceTree.toSet_finitelyMany _

/-- Congruence in the callee, with memory: replacing the body of a function
`@g` of a valid core module with one under which `@g`, run in the new module
from given memories, refines `@g` in the old, refines every function of the
module with memory, calls and recursion included, wherever a run names the
core's memories. It asks for no budget, whatever the parameter types of
`@g`, pointers included, and whatever the new body does to the memories:
every core op has finitely many outcomes. -/
theorem replaceBody_isRefinedBy_of_from (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (b : Region CoreDialect)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ Ty.isRefinedBy_refl
    Ty.isRefinedBy_trans (opsFinite lay ρ) hM hg b h hf).2

/-- Every function of the module other than `@g`, a caller of it or not,
is refined with memory by itself in the module with `@g`'s new body, under
the hypotheses of congruence in the callee from given memories: no budget,
whatever the parameter types of `@g` and whatever its new body does to the
memories. -/
theorem caller_isRefinedBy_of_from (hM : M.Valid) {g : Func CoreDialect}
    (hg : g ∈ M.funcs) (b : Region CoreDialect)
    (h : letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
          (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ M ⊑ f.memRuns lay ρ (M.replaceBody g.name b) := by
  have := replaceBody_isRefinedBy_of_from lay ρ hM hg b h hf
  change f.memRuns lay ρ M ⊑
    Func.memRuns lay ρ _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

/-- Congruence in the callee, with memory: replacing the body of a function
`@g` of a valid core module, which reaches no memory, with one under which
`@g`, run with memory in the new module, refines `@g` in the old, and under
which it reaches no memory in the new module, refines every function of the
module with memory, calls and recursion included, wherever a run names the
core's memories. It asks nothing of the parameter types of `@g`, pointers
included: its runs from given memories are its runs with memory, and
every core op has finitely many outcomes. -/
theorem replaceBody_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (b : Region CoreDialect) (hold : M.table.ReachesNoMemory g.name)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  Func.memRuns_replaceBody_isRefinedBy_of_opsFinite_memRuns lay ρ Ty.isRefinedBy_refl
    Ty.isRefinedBy_trans (opsIgnoreMemory lay ρ) (opsFinite lay ρ) hM hg b hold hmem h hf

/-- Every function of the module other than `@g`, a caller of it or not,
is refined with memory by itself in the module with `@g`'s new body, under
the hypotheses of congruence in the callee for a callee that touches no
memory. -/
theorem caller_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (b : Region CoreDialect) (hold : M.table.ReachesNoMemory g.name)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    (hf : f ∈ M.funcs) (hfg : f.name ≠ g.name) :
    f.memRuns lay ρ M ⊑ f.memRuns lay ρ (M.replaceBody g.name b) := by
  have := replaceBody_isRefinedBy lay ρ hM hg b hold hmem h hf
  change f.memRuns lay ρ M ⊑
    Func.memRuns lay ρ _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

end Fir.Core
