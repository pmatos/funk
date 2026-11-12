import Fir.Text.Grammar

/-!
# The data layout's text, proved

Each entry of a data layout has one spelling: decoding what an entry
writes gives the entry back when its numbers are within the limit, and an
attribute decodes only to an entry whose numbers are within it. What an
entry writes is a type in the grammar's sense, a word applied to
attributes that can be written, so the reader of types reads it back
(ADR-2026-11-12-1821).
-/

namespace Fir

theorem MemLayout.number_ofNat {n : Nat} (h : n ≤ MemLayout.limit) :
    MemLayout.number (n : Int) = some n := by
  have : (0 : Int) ≤ n ∧ (n : Int) ≤ MemLayout.limit := ⟨by omega, by exact_mod_cast h⟩
  simp [MemLayout.number, this]

theorem MemLayout.le_of_number {i : Int} {n : Nat} (h : MemLayout.number i = some n) :
    n ≤ MemLayout.limit := by
  unfold MemLayout.number at h
  split at h
  · cases h; omega
  · cases h

theorem ByteOrder.decode_word (o : ByteOrder) : ByteOrder.decode o.word = some o := by
  cases o <;> rfl

/-- Decoding what an entry writes gives it back, when its numbers are
within the limit. -/
theorem MemLayout.decode_attr {e : MemLayout} (h : e.InLimits) : MemLayout.decode e.attr = some e := by
  obtain ⟨mem, unit, pointer, order, align, ni⟩ := e
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hn := And.intro (MemLayout.number_ofNat h₁) <|
    And.intro (MemLayout.number_ofNat h₂) (MemLayout.number_ofNat h₃)
  cases align with
  | none =>
    cases ni <;> simp [MemLayout.attr, MemLayout.decode, MemLayout.decodeTail, hn,
      ByteOrder.decode_word]
  | some a =>
    have ha := MemLayout.number_ofNat (h₄ a rfl)
    cases ni <;> simp [MemLayout.attr, MemLayout.decode, MemLayout.decodeTail, hn, ha,
      ByteOrder.decode_word]

theorem MemLayout.decodeTail_le {as : List Attr} {a : Option Nat} {b : Bool}
    (h : MemLayout.decodeTail as = some (a, b)) : ∀ x ∈ a, x ≤ MemLayout.limit := by
  unfold MemLayout.decodeTail at h
  split at h
  · cases h; simp
  · split at h <;> cases h; simp
  · split at h
    · obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      simpa using MemLayout.le_of_number hn
    · cases h
  · split at h
    · obtain ⟨n, hn, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      simpa using MemLayout.le_of_number hn
    · cases h
  · cases h

/-- An attribute decodes only to an entry whose numbers are within the
limit. -/
theorem MemLayout.inLimits_of_decode {a : Attr} {e : MemLayout} (h : MemLayout.decode a = some e) :
    e.InLimits := by
  unfold MemLayout.decode at h
  split at h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨mem, h₁, unit, h₂, pointer, h₃, order, -, ⟨al, ni⟩, h₅, he⟩ := h
      cases he
      exact ⟨MemLayout.le_of_number h₁, MemLayout.le_of_number h₂, MemLayout.le_of_number h₃,
        MemLayout.decodeTail_le h₅⟩
    · cases h
  · cases h

/-- What an entry writes is a type: the word `memory` applied to attributes
that can be written. -/
theorem MemLayout.attr_isType (e : MemLayout) : e.attr.IsType := by
  have ho : isWord e.order.word := by cases e.order <;> decide
  obtain ⟨mem, unit, pointer, order, align, ni⟩ := e
  cases align <;> cases ni <;>
    simp only [MemLayout.attr, Attr.IsType, Attr.Writable, Attr.AllWritable, Option.map,
      Option.toList, List.cons_append, List.nil_append, ite_true, Bool.false_eq_true, ite_false,
      and_true, true_and, ho] <;> decide

end Fir
