import Fir.Core.LoadTextLaws
import Fir.Core.MemSetText

/-!
`memSet` reads back from how it is written, and only from it, for every
instance, valid or not: its name is `memset`, its one attribute is its
ordering, written as a word, and its operand types carry its memory, the
value's width and the length's width. The laws of the core dialect's text
use these facts.
-/

namespace Fir.Core

open Memory

/-- Each fill reads back from how it is written. -/
theorem decodeMemSet_loadAttrs (o : Memory.Ordering) (v w n : Nat) :
    decodeMemSet (loadAttrs o none) [.ptr n, .int v, .int w] [] = some (.memSet o v w n) := by
  simp [decodeMemSet, loadAttrs, decodeOrdering_word]

/-- A fill decodes only from its ordering, a pointer operand, two integer
operands and no result. -/
theorem decodeMemSet_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeMemSet as ts rs = some op) :
    op.name = "memset" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeMemSet at h
  split at h
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, by simp [Op.attrs, loadAttrs, word_of_decodeOrdering ho], rfl, rfl⟩
  · cases h

end Fir.Core
