import Fir.Core.LoadTextLaws
import Fir.Core.StoreText

/-!
`store` and `storePtr` read back from how they are written, and only from
it, for every instance, valid or not: its attributes are those of `load`, which are
written as tokens, and its operand types carry its width and memory. The
laws of the core dialect's text use these facts.
-/

namespace Fir.Core

open Memory

/-- Each `store` reads back from how it is written. -/
theorem decodeStore_loadAttrs (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat) :
    decodeStore (loadAttrs o a) [.int w, .ptr n] [] = some (.store o w a n) := by
  simp [decodeStore, decodeAccess_loadAttrs]

/-- Each `storePtr` reads back from how it is written. -/
theorem decodeStore_storePtr (o : Memory.Ordering) (mp : Nat) (a : Option Nat) (n : Nat) :
    decodeStore (loadAttrs o a) [.ptr mp, .ptr n] [] = some (.storePtr o mp a n) := by
  simp [decodeStore, decodeAccess_loadAttrs]

/-- `store` and `storePtr` decode only from their name, their attributes,
an integer or pointer operand and a pointer operand, and no result. -/
theorem decodeStore_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeStore as ts rs = some op) :
    op.name = "store" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeStore at h
  split at h <;> first
    | (obtain ⟨⟨o, a⟩, ha, rfl⟩ := Option.map_eq_some_iff.mp h
       exact ⟨rfl, loadAttrs_of_decodeAccess ha, rfl, rfl⟩)
    | cases h

end Fir.Core
