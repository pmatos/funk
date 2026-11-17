import Fir.Core.AllocaTextLaws
import Fir.Core.LoadText

/-!
`load`, `loadPtr` and `loadFloat` read back from how they are written, and only from
it, for every instance, valid or not: its ordering is one of seven words, and its
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

/-- The attributes of a load or a store read back as its ordering and its
alignment. -/
theorem decodeAccess_loadAttrs (o : Memory.Ordering) (a : Option Nat) :
    decodeAccess (loadAttrs o a) = some (o, a) := by
  simp [loadAttrs, decodeAccess, decodeOrdering_word, decodeAlign_toList]

/-- Attributes read as an ordering and an alignment are theirs. -/
theorem loadAttrs_of_decodeAccess {as : List Attr} {o : Memory.Ordering} {a : Option Nat}
    (h : decodeAccess as = some (o, a)) : loadAttrs o a = as := by
  unfold decodeAccess at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨o', ho, h⟩ := h
    obtain ⟨a', ha, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    simp [loadAttrs, word_of_decodeOrdering ho, toList_of_decodeAlign ha]
  · cases h

/-- Each `load` reads back from how it is written. -/
theorem decodeLoad_loadAttrs (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat) :
    decodeLoad (loadAttrs o a) [.ptr n] [.int w] = some (.load o w a n) := by
  simp [decodeLoad, decodeAccess_loadAttrs]

/-- Each `loadPtr` reads back from how it is written. -/
theorem decodeLoad_loadPtr (o : Memory.Ordering) (mp : Nat) (a : Option Nat) (n : Nat) :
    decodeLoad (loadAttrs o a) [.ptr n] [.ptr mp] = some (.loadPtr o mp a n) := by
  simp [decodeLoad, decodeAccess_loadAttrs]

/-- Each `loadFloat` reads back from how it is written. -/
theorem decodeLoad_loadFloat (o : Memory.Ordering) (e m : Nat) (a : Option Nat) (n : Nat) :
    decodeLoad (loadAttrs o a) [.ptr n] [.float e m] = some (.loadFloat o e m a n) := by
  simp [decodeLoad, decodeAccess_loadAttrs]

/-- `load`, `loadPtr` and `loadFloat` decode only from their name, their
attributes, a pointer operand and an integer, pointer or float result. -/
theorem decodeLoad_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeLoad as ts rs = some op) :
    op.name = "load" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeLoad at h
  split at h <;> first
    | (obtain ⟨⟨o, a⟩, ha, rfl⟩ := Option.map_eq_some_iff.mp h
       exact ⟨rfl, loadAttrs_of_decodeAccess ha, rfl, rfl⟩)
    | cases h

/-- `load`'s attributes are written as tokens. -/
theorem loadAttrs_writable (o : Memory.Ordering) (a : Option Nat) : Attr.AllWritable (loadAttrs o a) := by
  have ho : isWord o.word := by cases o <;> decide
  cases a <;> simp [loadAttrs, Attr.AllWritable, Attr.Writable, ho] <;> decide

end Fir.Core
