import Fir.Core.LoadTextLaws
import Fir.Core.StoreText

/-!
`store` reads back from how it is written, and only from it, for every
instance, valid or not: its attributes are those of `load`, which are
written as tokens, and its operand types carry its width and memory. The
laws of the core dialect's text use these facts.
-/

namespace Fir.Core

open Memory

/-- Each `store` reads back from how it is written. -/
theorem decodeStore_loadAttrs (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat) :
    decodeStore (loadAttrs o a) [.int w, .ptr n] [] = some (.store o w a n) := by
  simp [loadAttrs, decodeStore, decodeOrdering_word, decodeAlign_toList]

/-- `store` decodes only from its own name, its attributes, an integer and a
pointer operand, and no result. -/
theorem decodeStore_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeStore as ts rs = some op) :
    op.name = "store" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeStore at h
  split at h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨o, ho, h⟩ := h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨rfl, ?_, rfl, rfl⟩
      simp [Op.attrs, loadAttrs, word_of_decodeOrdering ho, toList_of_decodeAlign ha]
    · cases h
  · cases h

end Fir.Core
