import Fir.Core.EffectLaws
import Fir.Core.GlobalAddrLaws
import Fir.Core.FuncAddrLaws
import Fir.Core.PtrIntLaws
import Fir.Execution.AddressObligations

/-!
# The core dialect's addresses and declared allocations

Every core op meets the obligations of the section on addresses and the
declared allocation: where it does not declare an allocation, it gives no
allocation an address and counts no integer turned back into a pointer.

* Each op that touches no memory and reads no item of the run runs with
  memory by its rule in the set monad, so it keeps the memories.
* `alloca`, the loads and stores, `memCopy` and `memSet` run allocations,
  loads, stores and choices of bits, each of which keeps every address and
  count, and `fieldAddr`, `globalAddr` and `funcAddr` keep the memories.
* `ptrExpose` gives an address only in the memory of its pointer, and
  counts no rebuild; `ptrFromInt` counts a rebuild only in the memory of its
  pointer, and gives no address. Each declares an allocation in that
  memory, so each meets the obligations: exposing counts as allocating (the
  human's ruling of 2026-11-20 on #232, question B), and so does turning
  an integer back into a pointer (the human's ruling of 2026-11-21).
-/

namespace Fir.Core

open Memory

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems) (x : N)

/-- `alloca` keeps every address and count. -/
theorem alloca_keepsAddrs (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.alloca k t c a n) := fun _ =>
  ⟨fun _ => (alloc_keepsAddrs (unit := unitsOf lay) _ _ _ _ x).map (allocaResult n),
    fun h => nomatch h⟩

/-- `load` keeps every address and count. -/
theorem load_keepsAddrs (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.load o w a n) :=
  load_ownRuleHas o w a n lay ρ L fun
    | .poison => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
    | .value p => (Fir.load_keepsAddrs (unit := unitsOf lay) _ p _ _ x).map _

/-- `store` keeps every address and count. -/
theorem store_keepsAddrs (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.store o w a n) :=
  store_ownRuleHas o w a n lay ρ L fun
    | _, .poison => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
    | _, .value p => (Fir.store_keepsAddrs (unit := unitsOf lay) _ p _ _ x).map _

/-- `loadPtr` keeps every address and count. -/
theorem loadPtr_keepsAddrs (o : Memory.Ordering) (mp : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.loadPtr o mp a n) :=
  loadPtr_ownRuleHas o mp a n lay ρ L fun
    | .poison => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
    | .value p => (Fir.load_keepsAddrs (unit := unitsOf lay) _ p _ _ x).map _

/-- `storePtr` keeps every address and count. -/
theorem storePtr_keepsAddrs (o : Memory.Ordering) (mp : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.storePtr o mp a n) :=
  storePtr_ownRuleHas o mp a n lay ρ L fun
    | _, .poison => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
    | _, .value p => (Fir.store_keepsAddrs (unit := unitsOf lay) _ p _ _ x).map _

/-- `loadFloat` keeps every address and count. -/
theorem loadFloat_keepsAddrs (o : Memory.Ordering) (fe fm : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.loadFloat o fe fm a n) :=
  loadFloat_ownRuleHas o fe fm a n lay ρ L fun
    | .poison => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
    | .value p => (Fir.load_keepsAddrs (unit := unitsOf lay) _ p _ _ x).map _

/-- `storeFloat` keeps every address and count. -/
theorem storeFloat_keepsAddrs (o : Memory.Ordering) (fe fm : Nat) (a : Option Nat) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.storeFloat o fe fm a n) :=
  storeFloat_ownRuleHas o fe fm a n lay ρ L fun
    | _, .poison => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => nomatch h⟩
    | _, .value p => (Fir.store_keepsAddrs (unit := unitsOf lay) _ p _ _ x).map _

/-- `fieldAddr` keeps the memories. -/
theorem fieldAddr_keepsAddrs (s : String) (j n : Nat) (w : Option Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.fieldAddr s j n w) :=
  fieldAddr_ownRuleHas s j n w lay ρ L fun c => keepsAddrs_lift c

/-- `globalAddr` keeps the memories. -/
theorem globalAddr_keepsAddrs (s : String) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.globalAddr s n) :=
  globalAddr_ownRuleHas s n lay ρ L fun c => keepsAddrs_lift c

/-- `funcAddr` keeps the memories. -/
theorem funcAddr_keepsAddrs (s : String) (n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.funcAddr s n) :=
  funcAddr_ownRuleHas s n lay ρ L fun c => keepsAddrs_lift c

/-- `memCopy` keeps every address and count. -/
theorem memCopy_keepsAddrs (k : CopyKind) (o : Memory.Ordering) (w n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.memCopy k o w n) :=
  memCopy_ownRuleHas k o w n lay ρ L fun d s l =>
    memCopyRule_cases k w n lay ρ
      (copyLenRule_cases k n lay ρ (keepsAddrs_lift _) (fun _ => keepsAddrs_lift _)
        fun d s len => ((Fir.load_keepsAddrs (unit := unitsOf lay) _ s len 1 x).bind
          fun us => Fir.store_keepsAddrs _ d us 1 x).map _)
      (fun _ hf => KeepsAddrs.chooseBind hf) d s l

/-- `memSet` keeps every address and count. -/
theorem memSet_keepsAddrs (o : Memory.Ordering) (v w n : Nat) :
    OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) (.memSet o v w n) :=
  memSet_ownRuleHas o v w n lay ρ L fun p y l =>
    memSetRule_cases v w n lay ρ
      (setLenRule_cases v n lay ρ (keepsAddrs_lift _) (fun _ => keepsAddrs_lift _)
        fun q us => (Fir.store_keepsAddrs (unit := unitsOf lay) _ q us 1 x).map _)
      (fun _ hf => KeepsAddrs.chooseBind hf) p y l

end

/-- The core dialect's declarations cover addresses and rebuilds: each op
keeps the addresses and the count of every memory where it does not declare
an allocation. -/
theorem lawfulDialectAddresses : LawfulDialectAddresses CoreDialect :=
  LawfulDialectAddresses.ofKeeps fun op _ _ _ _ lay ρ L x hx => Op.memCases (P := fun op =>
      ¬ ((Fir.effects (d := CoreDialect) op).allocates.map ρ).Has x →
        OwnRuleHas lay ρ L (KeepsAddrs x) (d := CoreDialect) op) op
    (fun op hm hi _ => OwnRuleHas.ofLifts (Op.liftsSetM op hm hi) lay ρ L fun c => keepsAddrs_lift c)
    (fun k t c a n _ => alloca_keepsAddrs lay ρ L x k t c a n)
    (fun o w a n _ => load_keepsAddrs lay ρ L x o w a n)
    (fun o w a n _ => store_keepsAddrs lay ρ L x o w a n)
    (fun o mp a n _ => loadPtr_keepsAddrs lay ρ L x o mp a n)
    (fun o mp a n _ => storePtr_keepsAddrs lay ρ L x o mp a n)
    (fun o e m a n _ => loadFloat_keepsAddrs lay ρ L x o e m a n)
    (fun o e m a n _ => storeFloat_keepsAddrs lay ρ L x o e m a n)
    (fun s j n w _ => fieldAddr_keepsAddrs lay ρ L x s j n w)
    (fun s n _ => globalAddr_keepsAddrs lay ρ L x s n)
    (fun s n _ => funcAddr_keepsAddrs lay ρ L x s n)
    (fun k o w n _ => memCopy_keepsAddrs lay ρ L x k o w n)
    (fun o v w n _ => memSet_keepsAddrs lay ρ L x o v w n)
    (fun n w hx => OwnRuleHas.keeps (ptrExpose_exposesNot n w lay ρ L x hx)
      (ptrExpose_rebuildsNot n w lay ρ L x))
    (fun n w hx => OwnRuleHas.keeps (ptrFromInt_exposesNot n w lay ρ L x)
      (ptrFromInt_rebuildsNot n w lay ρ L x hx)) hx

end Fir.Core

namespace Fir

instance : LawfulDialectAddresses CoreDialect := Core.lawfulDialectAddresses

end Fir
