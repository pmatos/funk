import Fir.Core.EffectLaws
import Fir.Execution.MemoryModes

/-!
# The core dialect in the tree of choices

The core dialect's rules run in the tree of choices. Each op runs its rule,
the same rule that the set monad's semantics runs; an op without rules ends
its path with no outcome, for that op, as the set monad gives it none
(`docs/decisions/fir-ref.md#an-op-without-rules`). `fir-ref` reports such a
path as an error.

`fir-ref run` runs the core with memory, in the state layer over the tree of
choices, where the run's memories have their layout entries, the run names
the core's memories and gives each op the items of its module. Each op runs
by its rule with memory in that layer, as it does in the core's semantics
with memory in the layer over the set monad, and `toSet` through the layer
keeps choice, UB, allocation, loads and stores, so it maps the one to the
other at every layout and naming of the core's memories and every record
of items. The modes of the next section walk the run in that layer.
-/

namespace Fir.Core

open Memory

/-- The core dialect's rules in the tree of choices. An op without rules
ends its path with no outcome, and names itself. -/
instance : DialectDenote CoreDialect (ChoiceTree Op) := denoteIn fun op => .noOutcome op

/-- The core dialect's semantics in the state layer over the tree of
choices, where a run's memories have the layout entries `lay`, the run
names the core's memory `x` as `ρ x` and gives each op the items `L`: each
op runs by its rule with memory in the layer, and an op with no rule ends
its path with no outcome. -/
@[instance_reducible] def memTreeDenote {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : Mem → N) (L : RunItems) :
    DialectDenote CoreDialect (StateT (Memories N (unitsOf lay)) (ChoiceTree Op)) :=
  memDenoteIn lay ρ L fun op _ => ChoiceTree.noOutcome op

variable {N : Type} [DecidableEq N] (lay : N → MemLayout)

/-- The core's semantics in the layer over the tree of choices denotes its
semantics with memory, wherever a run names the core's memories, whatever
their entries, whatever the items it gives: `toSet` through the layer keeps
choice and UB, op by op. -/
theorem memMapsDenote (ρ : DialectEffects.Mem CoreDialect → N) (L : RunItems) :
    letI := memTreeDenote lay ρ L
    MemMapsDenote (d := CoreDialect) lay (ε := Op) ρ L :=
  memDenoteIn_mapsDenote lay ρ L (ChoiceTree.toSetState Op _) (ChoiceTree.toSetState_keeps Op _)
    (fun x k size al => ChoiceTree.toSetMorphism.state_alloc x k size al)
    (fun x p k al => ChoiceTree.toSetMorphism.state_load ChoiceTree.toSet_keeps.ub x p k al)
    (fun x p us al => ChoiceTree.toSetMorphism.state_store ChoiceTree.toSet_keeps.ub x p us al)
    (fun op _ => ChoiceTree.noOutcome op) (fun _ _ _ => False) fun _ => rfl

end Fir.Core
