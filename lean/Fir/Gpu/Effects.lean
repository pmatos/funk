import Fir.Gpu.Ops
import Fir.Core.Poison

/-!
The effects of `gpu` (ADR-2026-11-09-1541). An op of `gpu` gives a fact
about the work-item that runs it: an id or a size, which is fixed for the
whole run of the work-item. So it reads no memory, writes none, allocates
none, is never UB and never makes poison: its effect set is empty. It takes
no operand, so it propagates poison trivially.

`gpu` has no memory of its own yet: its memories are the core's
(`DialectMemOver`). How its work-group memory meets the data layout's
memory numbers waits for the human's ruling (#212, stage 3). The section
on the dialect's execution rules proves these declarations sound, at every
work-item (`Gpu.lawfulDialectEffects`).
-/

namespace Fir.Gpu

/-- Every op of `gpu` is pure and propagates poison. Its memories are the
core's, and none of its own. -/
instance instDialectEffects : DialectEffects GpuDialect :=
  ⟨DialectEffects.Mem CoreDialect ⊕ Empty, fun _ => .propagates, fun _ => {}⟩

/-- `gpu` names the core's memories as the core does, and has none of its
own. -/
instance instDialectMemOver : DialectMemOver CoreDialect GpuExt := ⟨Empty, id, id, fun _ => rfl, fun _ => rfl⟩

end Fir.Gpu
