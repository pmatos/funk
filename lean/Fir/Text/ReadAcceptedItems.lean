import Fir.Text.ReadAcceptedBlocks

/-!
# Items as read

On tokens that can be written, the readers of items give items that can be
written. An item's parameters come from the reader of definitions, its
result types from the reader of types, and its body from the reader of
blocks, or from the readers of a dialect set and of items when it starts
with a word, and its attributes from the reader of attributes. Nothing is
asked of its kind or its symbol: decoding checks the kind, whatever the
symbol.

The reader of items and the reader of one item call one another, for the
items of a body. They are proved together, by induction that follows their
own recursion, as the readers of blocks are.
-/

namespace Fir.Text

/-- The name of a dialect as read is a word. -/
theorem readDialectName_writable (ts : List Token) :
    ReadsWritable readDialectName (fun x => isWord x) ts := by
  intro hw a r h
  unfold readDialectName at h
  split at h
  · cases h
    exact ⟨hw.word, hw.tail⟩
  · exact absurd h fail_ne_ok

/-- The names of a dialect set as read are words. -/
theorem readDialects_writable (ts : List Token) :
    ReadsWritable readDialects (fun xs => ∀ x ∈ xs, isWord x) ts := by
  intro hw a r h
  unfold readDialects at h
  split at h
  · bind_step h with ⟨⟨n, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨ns, r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readDialectName_writable _ hw.tail _ _ e₁
    obtain ⟨k₂, w₂⟩ := readMore_writable readDialectName_writable _ w₁ _ _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  · cases h
    exact ⟨by simp, hw⟩

/-- On tokens that can be written, the reader of a data layout reads
entries written as types. -/
theorem readLayout_writable (ts : List Token) :
    ReadsWritable readLayout (fun es => ∀ e ∈ es, e.1.IsType) ts := by
  intro hw a r h
  unfold readLayout at h
  split at h
  · bind_step h with ⟨⟨e, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨es, r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readType_writable _ hw.tail _ _ e₁
    obtain ⟨k₂, w₂⟩ := readMore_writable readType_writable _ w₁ _ _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  · cases h
    exact ⟨by simp, hw⟩

/-- On tokens that can be written, the readers of items give items that can
be written. -/
theorem readItems_writable :
    ∀ top ts, ReadsWritable (readItems top) (fun is => ∀ i ∈ is, i.Writable) ts := by
  intro top ts
  induction top, ts using readItems.induct
    (motive2 := fun kind p ts => ReadsWritable (readItem kind p) SItem.Writable ts) with
  | case1 top w p rest hl => -- `readItems`: `locs` ends the items of the module
    intro hw is r h
    rw [readItems.eq_1, ite_eq_left hl] at h
    cases h
    exact ⟨by simp, hw⟩
  | case2 top w p rest hl ihi ihis => -- `readItems`: an item, then the items after it
    intro hw is r h
    rw [readItems.eq_1, ite_eq_right hl] at h
    bind_step h with ⟨⟨i, r₁, h₁⟩, e₁, h⟩
    bind_step h with ⟨⟨is', r₂, h₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := ihi hw.tail _ _ e₁
    obtain ⟨k₂, w₂⟩ := ihis r₁ h₁ w₁ _ _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  | case3 top ts hne => -- `readItems`: no item
    intro hw is r h
    rw [readItems.eq_2 _ _ hne] at h
    cases h
    exact ⟨by simp, hw⟩
  | case4 kind p name pos rest ih => -- `readItem`
    intro hw i r h
    rw [readItem.eq_1] at h
    bind_step h with ⟨⟨_, r₁, h₁⟩, e₁, h⟩
    have w₁ := (expect_writable _ _ _ hw.tail _ _ e₁).2
    bind_step h with ⟨⟨params, r₂, h₂⟩, e₂, h⟩
    have k₂ : (∀ x ∈ params, x.Writable) ∧ TokensWritable r₂ := by
      split at e₂
      · cases e₂
        exact ⟨by simp, w₁⟩
      · exact readDefs_writable _ w₁ _ _ e₂
    bind_step h with ⟨⟨_, r₃, h₃⟩, e₃, h⟩
    have w₃ := (expect_writable _ _ _ k₂.2 _ _ e₃).2
    bind_step h with ⟨⟨results, r₄, h₄⟩, e₄, h⟩
    have k₄ : (∀ x ∈ results, x.1.IsType) ∧ TokensWritable r₄ := by
      split at e₄
      · bind_step e₄ with ⟨⟨t, a⟩, f₁, e₄⟩
        bind_step e₄ with ⟨⟨more, b⟩, f₂, e₄⟩
        cases e₄
        obtain ⟨j₁, v₁⟩ := readType_writable _ w₃.tail _ _ f₁
        obtain ⟨j₂, v₂⟩ := readMore_writable readType_writable _ v₁ _ _ f₂
        exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ j₁) (j₂ y), v₂⟩
      · cases e₄
        exact ⟨by simp, w₃⟩
    bind_step h with ⟨⟨attrs, r₅, h₅⟩, e₅, h⟩
    have k₅ := readAttrs_writable _ k₄.2 _ _ e₅
    have w₅ := k₅.2
    bind_step h with ⟨⟨_, r₆, h₆⟩, e₆, h⟩
    have w₆ := (expect_writable _ _ _ w₅ _ _ e₆).2
    bind_step h with ⟨⟨body, r₇, h₇⟩, e₇, h⟩
    have k₇ : body.Writable ∧ TokensWritable r₇ := by
      split at e₇
      · bind_step e₇ with ⟨⟨ds, r, hr⟩, f₁, e₇⟩
        bind_step e₇ with ⟨⟨is, r', hr'⟩, f₂, e₇⟩
        cases e₇
        obtain ⟨j₁, v₁⟩ := readDialects_writable _ w₆ _ _ f₁
        obtain ⟨j₂, v₂⟩ := ih r₁ h₁ r₂ h₂ r₃ h₃ r₄ h₄ r₅ h₅ [] _ _ _ (by assumption) r hr v₁ _ _ f₂
        exact ⟨⟨j₁, (SItem.writableList_iff is).mpr j₂⟩, v₂⟩
      · bind_step e₇ with ⟨⟨bs, a⟩, f₁, e₇⟩
        cases e₇
        exact readBlocks_writable _ w₆ _ _ f₁
    bind_step h with ⟨⟨_, r₈, h₈⟩, e₈, h⟩
    cases h
    exact ⟨(SItem.writable_iff _).mpr ⟨k₂.1, k₄.1, k₅.1, k₇.1⟩,
      (expect_writable _ _ _ k₇.2 _ _ e₈).2⟩
  | case5 kind p ts hne => -- `readItem`: no symbol
    intro hw i r h
    rw [readItem.eq_2 _ _ _ hne] at h
    exact absurd h fail_ne_ok

end Fir.Text
