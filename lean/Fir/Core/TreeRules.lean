import Fir.Core.EffectLaws
import Fir.Execution.MemoryModes

/-!
# The core dialect in the tree of choices

`fir-ref run` runs the core dialect's rules in the tree of choices. Each op
runs its rule, the same rule that the set monad's semantics runs; an op without
rules ends its path with no outcome, for that op, as the set monad gives it
none (`docs/decisions/fir-ref.md#an-op-without-rules`). `fir-ref` reports such
a path as an error.

Each op's semantics in the tree has the set monad's as its set: the rules
are written once for any monad, and `toSet` keeps choice and UB, so it maps
each op's rule in the tree to its rule in the set monad (the section on the
core's rules with memory).

With memory, the core runs in the state layer over the tree of choices,
where the run's memories have their layout entries and the run names the
core's memories. Each op runs by its rule with memory in that layer, as it
does in the core's semantics with memory in the layer over the set monad,
and `toSet` through the layer keeps choice and UB, so it maps the one to the
other at every layout and naming of the core's memories. No core op touches
memory yet, so lifting into the layer maps each op's rule in the tree to
its rule with memory there. The modes of the next section walk the run in
that layer.
-/

namespace Fir.Core

open Memory

/-- The core dialect's rules in the tree of choices. An op without rules
ends its path with no outcome, and names itself. -/
instance : DialectDenote CoreDialect (ChoiceTree Op) := denoteIn fun op => .noOutcome op

/-- The tree's semantics of each core op denotes the set monad's: `toSet`
keeps choice and UB, and an op with no rule has no outcome in both. -/
theorem mapsDenote : (ChoiceTree.toSetMorphism (ε := Op)).MapsDenote (d := CoreDialect) :=
  denoteIn_mapsDenote _ ChoiceTree.toSet_keeps (fun op => .noOutcome op) (fun _ _ => False)
    fun _ => rfl

/-- The core dialect's semantics in the state layer over the tree of
choices, where a run's memories have the layout entries `lay` and the run
names the core's memory `x` as `ρ x`: each op runs by its rule with memory
in the layer, and an op with no rule ends its path with no outcome. -/
@[instance_reducible] def memTreeDenote {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : Mem → N) :
    DialectDenote CoreDialect (StateT (Memories N (unitsOf lay)) (ChoiceTree Op)) :=
  memDenoteIn lay ρ fun op _ => ChoiceTree.noOutcome op

variable {N : Type} [DecidableEq N] (lay : N → MemLayout)

/-- The core's semantics in the layer over the tree of choices denotes its
semantics with memory, wherever a run names the core's memories, whatever
their entries: `toSet` through the layer keeps choice and UB, op by op. -/
theorem memMapsDenote (ρ : DialectEffects.Mem CoreDialect → N) :
    letI := memTreeDenote lay ρ
    MemMapsDenote (d := CoreDialect) lay (ε := Op) ρ :=
  memDenoteIn_mapsDenote lay ρ (ChoiceTree.toSetState Op _) (ChoiceTree.toSetState_keeps Op _)
    (fun op _ => ChoiceTree.noOutcome op) (fun _ _ _ => False) fun _ => rfl

/-- No core op touches memory, so lifting into the layer over the tree maps
each op's rule in the tree to its rule with memory in the layer, at every
layout and naming. -/
theorem memTree_liftState (ρ : Mem → N) :
    letI := memTreeDenote lay ρ
    (MonadMorphism.liftState (ChoiceTree Op) (Memories N (unitsOf lay))).MapsDenote
      (d := CoreDialect) :=
  denoteIn_mapsDenote (MonadMorphism.liftState (ChoiceTree Op) _)
    (MonadMorphism.liftState_keeps _ fun _ _ => rfl) (fun op => ChoiceTree.noOutcome op)
    (fun op _ => ChoiceTree.noOutcome op) fun _ => rfl

end Fir.Core
