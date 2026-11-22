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

/-- A parameter of an item as read can be written: its definition and its
attributes. -/
theorem readParam_writable (ts : List Token) :
    ReadsWritable readParam (fun x => x.1.Writable ∧ ∀ a ∈ x.2, a.1.Writable) ts := by
  intro hw x r h
  unfold readParam at h
  bind_step h with ⟨⟨y, a⟩, e₁, h⟩
  bind_step h with ⟨⟨as, b⟩, e₂, h⟩
  cases h
  obtain ⟨k₁, w₁⟩ := readDef_writable _ hw _ _ e₁
  obtain ⟨k₂, w₂⟩ := readAttrs_writable _ w₁ _ _ e₂
  exact ⟨⟨k₁, k₂⟩, w₂⟩

/-- The parameters of an item after its first, as read, can be written. -/
theorem readMoreParams_writable : ∀ ts, ReadsWritable readMoreParams
    (fun ps => ∀ x ∈ ps.1, x.1.Writable ∧ ∀ a ∈ x.2, a.1.Writable) ts := by
  intro ts
  induction ts using readMoreParams.induct with
  | case1 _ _ rest =>
    intro hw xs r h
    rw [readMoreParams.eq_1] at h
    cases h
    exact ⟨by simp, hw.tail.tail⟩
  | case2 _ rest hne ih =>
    intro hw xs r h
    rw [readMoreParams.eq_2 _ _ hne] at h
    bind_step h with ⟨⟨x, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨⟨xs', v⟩, r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readParam_writable _ hw.tail x _ e₁
    obtain ⟨k₂, w₂⟩ := ih r₁ hr₁ w₁ _ _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  | case3 ts h₁ h₂ =>
    intro hw xs r h
    rw [readMoreParams.eq_3 _ h₁ h₂] at h
    cases h
    exact ⟨by simp, hw⟩

/-- The parameters of an item as read can be written. -/
theorem readParams_writable (ts : List Token) : ReadsWritable readParams
    (fun ps => ∀ x ∈ ps.1, x.1.Writable ∧ ∀ a ∈ x.2, a.1.Writable) ts := by
  intro hw xs r h
  unfold readParams at h
  split at h
  · cases h
    exact ⟨by simp, hw.tail⟩
  · bind_step h with ⟨⟨x, a⟩, e₁, h⟩
    bind_step h with ⟨⟨⟨xs', v⟩, b⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readParam_writable _ hw _ _ e₁
    obtain ⟨k₂, w₂⟩ := readMoreParams_writable _ w₁ _ _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩

/-- A result of an item as read can be written: its type and its
attributes. -/
theorem readResult_writable (ts : List Token) :
    ReadsWritable readResult (fun x => x.1.1.IsType ∧ ∀ a ∈ x.2, a.1.Writable) ts := by
  intro hw x r h
  unfold readResult at h
  bind_step h with ⟨⟨y, a⟩, e₁, h⟩
  bind_step h with ⟨⟨as, b⟩, e₂, h⟩
  cases h
  obtain ⟨k₁, w₁⟩ := readType_writable _ hw _ _ e₁
  obtain ⟨k₂, w₂⟩ := readAttrs_writable _ w₁ _ _ e₂
  exact ⟨⟨k₁, k₂⟩, w₂⟩

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
    have k₂ : (∀ x ∈ params.1, x.1.Writable ∧ ∀ a ∈ x.2, a.1.Writable) ∧ TokensWritable r₂ := by
      split at e₂
      · cases e₂
        exact ⟨by simp, w₁⟩
      · exact readParams_writable _ w₁ _ _ e₂
    bind_step h with ⟨⟨_, r₃, h₃⟩, e₃, h⟩
    have w₃ := (expect_writable _ _ _ k₂.2 _ _ e₃).2
    bind_step h with ⟨⟨results, r₄, h₄⟩, e₄, h⟩
    have k₄ : (∀ x ∈ results, x.1.1.IsType ∧ ∀ a ∈ x.2, a.1.Writable) ∧ TokensWritable r₄ := by
      split at e₄
      · bind_step e₄ with ⟨⟨t, a⟩, f₁, e₄⟩
        bind_step e₄ with ⟨⟨more, b⟩, f₂, e₄⟩
        cases e₄
        obtain ⟨j₁, v₁⟩ := readResult_writable _ w₃.tail _ _ f₁
        obtain ⟨j₂, v₂⟩ := readMore_writable readResult_writable _ v₁ _ _ f₂
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
    refine ⟨(SItem.writable_iff _).mpr ⟨?_, ?_, ?_, k₇.1, ?_, ?_, by simp, by simp⟩,
      (expect_writable _ _ _ k₇.2 _ _ e₈).2⟩
    · simpa using fun x as hx => (k₂.1 (x, as) hx).1
    · simpa using fun a b as hx => (k₄.1 ((a, b), as) hx).1
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases hl : results.getLast? with _ | l
        · simp [hl] at ha
        · simp only [hl, Option.map_some, Option.getD_some] at ha
          exact (k₄.1 _ (List.mem_of_getLast? hl)).2 _ ha
      · exact k₅.1 _ ha
    · simpa using fun x _ hx => (k₂.1 _ hx).2
    · simp only [List.mem_map]
      rintro _ ⟨x, hx, rfl⟩
      exact (k₄.1 _ (List.dropLast_subset _ hx)).2
  | case5 kind p ts hne => -- `readItem`: no symbol
    intro hw i r h
    rw [readItem.eq_2 _ _ _ hne] at h
    exact absurd h fail_ne_ok

end Fir.Text
