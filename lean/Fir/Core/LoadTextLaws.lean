import Fir.Core.AllocaTextLaws
import Fir.Core.LoadText

/-!
`load` reads back from how it is written, and only from it, for every
instance, valid or not: its ordering is one of seven words, and its
alignment is written as `align(A)` when it has one. Its attributes are
written as tokens. The laws of the core dialect's text use these facts.
-/

namespace Fir.Core

open Memory

/-- The word of an ordering is the only one that names it. -/
theorem word_of_decodeOrdering {w : String} {o : Memory.Ordering} (h : decodeOrdering w = some o) :
    o.word = w := by
  unfold decodeOrdering at h
  split at h <;> cases h <;> rfl

/-- Each `load` reads back from how it is written. -/
theorem decodeLoad_loadAttrs (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat) :
    decodeLoad (loadAttrs o a) [.ptr n] [.int w] = some (.load o w a n) := by
  simp [loadAttrs, decodeLoad, decodeOrdering_word, decodeAlign_toList]

/-- `load` decodes only from its own name, its attributes, a pointer operand
and an integer result. -/
theorem decodeLoad_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeLoad as ts rs = some op) :
    op.name = "load" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeLoad at h
  split at h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨o, ho, h⟩ := h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨rfl, ?_, rfl, rfl⟩
      simp [Op.attrs, loadAttrs, word_of_decodeOrdering ho, toList_of_decodeAlign ha]
    · cases h
  · cases h

/-- `load`'s attributes are written as tokens. -/
theorem loadAttrs_writable (o : Memory.Ordering) (a : Option Nat) : Attr.AllWritable (loadAttrs o a) := by
  have ho : isWord o.word := by cases o <;> decide
  cases a <;> simp [loadAttrs, Attr.AllWritable, Attr.Writable, ho] <;> decide

end Fir.Core
