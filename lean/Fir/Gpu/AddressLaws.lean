import Fir.Gpu.Runs
import Fir.Sum.AddressLaws
import Fir.Core.AddressLaws

/-!
# `gpu`'s addresses and declared allocations

Every op of `gpu` keeps every address and count: a question touches no
memory and keeps the memories, and `gpu.work_group_alloca` allocates, which
gives no address and counts no rebuild. So `gpu` meets the obligations of
the section on addresses and the declared allocation, and the sum
`CoreGpu` meets them, since both sides do.
-/

namespace Fir.Gpu

open Memory

variable [WorkItem]

/-- `gpu.work_group_alloca` keeps every address and count. -/
theorem Op.alloc_keepsAddrs (t : Core.Ty) (c : Nat) (a : Option Nat) (n : Nat) {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems)
    (x : N) : OwnRuleHas lay ρ L (KeepsAddrs x) (d := GpuDialect) (.alloc t c a n) := fun _ =>
  ⟨fun _ => (Fir.alloc_keepsAddrs (unit := unitsOf lay) _ _ _ _ x).map (allocResult t c a n),
    fun h => nomatch h⟩

/-- `gpu`'s declarations cover addresses and rebuilds at every work-item. -/
instance lawfulAddresses : LawfulDialectAddresses GpuDialect :=
  LawfulDialectAddresses.ofKeeps fun op _ _ _ _ lay ρ L x _ => Op.memCases
    (P := fun op => OwnRuleHas lay ρ L (KeepsAddrs x) (d := GpuDialect) op) op
    (fun q d w => OwnRuleHas.ofLifts (query_liftsSetM q d w) lay ρ L fun c => keepsAddrs_lift c)
    fun t c a n => Op.alloc_keepsAddrs t c a n lay ρ L x

/-- The sum's declarations cover addresses and rebuilds, since both sides'
do. -/
instance coreGpu_lawfulAddresses : LawfulDialectAddresses CoreGpu :=
  Dialect.sum.lawfulAddresses fun _ h => h

end Fir.Gpu
