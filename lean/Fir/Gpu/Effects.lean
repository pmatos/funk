import Fir.Gpu.Ops
import Fir.Core.Poison

/-!
The effects of `gpu` (ADR-2026-11-09-1541). A question of `gpu` gives a
fact about the work-item that runs it: an id or a size, which is fixed for
the whole run of the work-item. So it reads no memory, writes none,
allocates none, is never UB and never makes poison: its effect set is
empty. `gpu.work_group_alloca` allocates in the memory of its result, as
`alloca` does: it is never UB and its result is a defined pointer, so
allocating is its only effect. Neither takes an operand, so each propagates
poison trivially.

`gpu` gives a declared memory its meaning, and has no memory of its own:
work-group memory is a memory of the host's data layout, named by its
number, as the core names it (the human's ruling of 2026-11-16 on #212).
So its memories are the core's (`DialectMemOver`), and an allocation's
effect names the core's memory of its result. The section on the dialect's
execution rules proves these declarations sound, at every work-item
(`Gpu.lawfulDialectEffects`).
-/

namespace Fir.Gpu

/-- The effects of each op of `gpu`: none for a question, and an
allocation in the memory of its result for `gpu.work_group_alloca`. -/
def Op.effects : Op → Effects (DialectEffects.Mem CoreDialect ⊕ Empty)
  | .query .. => {}
  | .alloc _ _ _ n => { allocates := .these [.inl n] }

/-- Every op of `gpu` propagates poison. Its memories are the core's, and
none of its own. -/
instance instDialectEffects : DialectEffects GpuDialect :=
  ⟨DialectEffects.Mem CoreDialect ⊕ Empty, fun _ => .propagates, Op.effects⟩

/-- `gpu` names the core's memories as the core does, and has none of its
own. -/
instance instDialectMemOver : DialectMemOver CoreDialect GpuExt := ⟨Empty, id, id, fun _ => rfl, fun _ => rfl⟩

end Fir.Gpu
