import Fir.Core.LoadTextLaws
import Fir.Core.MemCopyText

/-!
`memCopy` reads back from how it is written, and only from it, for every
instance, valid or not: its name is its kind's, its one attribute is its
ordering, written as a word, and its operand types carry its memory and the
length's width. The laws of the core dialect's text use these facts.
-/

namespace Fir.Core

open Memory

/-- Each copy and each move reads back from how it is written. -/
theorem decodeMemCopy_loadAttrs (k : CopyKind) (o : Memory.Ordering) (w n : Nat) :
    decodeMemCopy k (loadAttrs o none) [.ptr n, .ptr n, .int w] [] = some (.memCopy k o w n) := by
  simp [decodeMemCopy, loadAttrs, decodeOrdering_word]

/-- A copy or a move decodes only from its kind's name, its ordering, two
pointer operands of one memory, an integer operand and no result. -/
theorem decodeMemCopy_eq {k : CopyKind} {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeMemCopy k as ts rs = some op) :
    op.name = k.name ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeMemCopy at h
  split at h
  · split at h
    · rename_i hn
      subst hn
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨rfl, by simp [Op.attrs, loadAttrs, word_of_decodeOrdering ho], rfl, rfl⟩
    · cases h
  · cases h

/-- The names of a copy and a move are words. -/
theorem CopyKind.name_isWord (k : CopyKind) : isWord k.name := by
  cases k <;> decide

end Fir.Core
