import Fir.Text.ReadAcceptedItems

/-!
# The location table and the module as read

Every number that the location table holds is below 2³². Its
references, the keys of its entries and the references inside callsite,
fused and derived locations, come from location reference tokens, which
the lexer bounds. Its lines and columns come from integer tokens, which the
lexer does not bound: the reader of a line or a column checks each of them
where it stands.

The result is the grammar step: on tokens that can be written, the reader
of a module gives a tree that can be written. With the lexer's step, the
first two steps of the parser give a tree that can be written from every
text that they accept.
-/

namespace Fir.Text

/-- A line or a column as read is below `2^32`: `readNat` checks it. -/
theorem readNat_writable (what : String) (ts : List Token) :
    ReadsWritable (readNat what) (· < Location.limit) ts := by
  intro hw n r h
  unfold readNat at h
  split at h
  · split at h
    · cases h
      exact ⟨by assumption, hw.tail⟩
    · cases h
  · exact absurd h fail_ne_ok

/-- A location reference inside a location comes from a location reference
token, so it is below `2^32`. -/
theorem readLocRef_writable (ts : List Token) :
    ReadsWritable readLocRef (· < Location.limit) ts := by
  intro hw n r h
  unfold readLocRef at h
  split at h
  · cases h
    exact ⟨hw.locRef, hw.tail⟩
  · exact absurd h fail_ne_ok

/-- The lines and columns of a source range are below `2^32`. -/
theorem readRange_writable (file : String) (ts : List Token) :
    ReadsWritable (readRange file) Location.InLimits ts := by
  intro hw l r h
  unfold readRange at h
  bind_step h with ⟨⟨_, a⟩, e₁, h⟩
  bind_step h with ⟨⟨l₁, b⟩, e₂, h⟩
  bind_step h with ⟨⟨_, c⟩, e₃, h⟩
  bind_step h with ⟨⟨c₁, d⟩, e₄, h⟩
  bind_step h with ⟨⟨_, e⟩, e₅, h⟩
  bind_step h with ⟨⟨l₂, f⟩, e₆, h⟩
  bind_step h with ⟨⟨_, g⟩, e₇, h⟩
  bind_step h with ⟨⟨c₂, i⟩, e₈, h⟩
  cases h
  have w₁ := (expect_writable _ _ _ hw _ _ e₁).2
  obtain ⟨k₂, w₂⟩ := readNat_writable _ _ w₁ _ _ e₂
  have w₃ := (expect_writable _ _ _ w₂ _ _ e₃).2
  obtain ⟨k₄, w₄⟩ := readNat_writable _ _ w₃ _ _ e₄
  have w₅ := (keyword_writable _ _ w₄ _ _ e₅).2
  obtain ⟨k₆, w₆⟩ := readNat_writable _ _ w₅ _ _ e₆
  have w₇ := (expect_writable _ _ _ w₆ _ _ e₇).2
  obtain ⟨k₈, w₈⟩ := readNat_writable _ _ w₇ _ _ e₈
  refine ⟨?_, w₈⟩
  simp only [Location.InLimits, Location.numbers, List.mem_cons, List.not_mem_nil, or_false]
  rintro n (rfl | rfl | rfl | rfl) <;> assumption

/-- The references of a `callsite`, `fused` or `derived` location are below
`2^32`, and a `name` has none. -/
theorem readLocArgs_writable (kind : String) (ts : List Token) :
    ReadsWritable (readLocArgs kind) Location.InLimits ts := by
  intro hw l r h
  unfold readLocArgs at h
  bind_step h with ⟨⟨loc, a⟩, e₁, h⟩
  have k : Location.InLimits loc ∧ TokensWritable a.1 := by
    split at e₁
    · split at e₁
      · cases e₁
        exact ⟨by simp [Location.InLimits, Location.numbers, Location.refs], hw.tail⟩
      · exact absurd e₁ fail_ne_ok
    · bind_step e₁ with ⟨⟨callee, a₁⟩, f₁, e₁⟩
      bind_step e₁ with ⟨⟨_, a₂⟩, f₂, e₁⟩
      bind_step e₁ with ⟨⟨caller, a₃⟩, f₃, e₁⟩
      cases e₁
      obtain ⟨k₁, w₁⟩ := readLocRef_writable _ hw _ _ f₁
      have w₂ := (keyword_writable _ _ w₁ _ _ f₂).2
      obtain ⟨k₃, w₃⟩ := readLocRef_writable _ w₂ _ _ f₃
      refine ⟨?_, w₃⟩
      simp only [Location.InLimits, Location.numbers, Location.refs, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro n (rfl | rfl) <;> assumption
    · split at e₁
      · cases e₁
        exact ⟨by simp [Location.InLimits, Location.numbers, Location.refs], hw⟩
      · bind_step e₁ with ⟨⟨x, a₁⟩, f₁, e₁⟩
        bind_step e₁ with ⟨⟨xs, a₂⟩, f₂, e₁⟩
        cases e₁
        obtain ⟨k₁, w₁⟩ := readLocRef_writable _ hw _ _ f₁
        obtain ⟨k₂, w₂⟩ := readMore_writable readLocRef_writable _ w₁ _ _ f₂
        refine ⟨?_, w₂⟩
        simp only [Location.InLimits, Location.numbers, Location.refs]
        exact fun n hn => (List.mem_cons.mp hn).elim (· ▸ k₁) (k₂ n)
    · bind_step e₁ with ⟨⟨src, a₁⟩, f₁, e₁⟩
      cases e₁
      obtain ⟨k₁, w₁⟩ := readLocRef_writable _ hw _ _ f₁
      refine ⟨?_, w₁⟩
      simpa [Location.InLimits, Location.numbers, Location.refs] using k₁
  bind_step h with ⟨⟨_, b⟩, e₂, h⟩
  cases h
  exact ⟨k.1, (expect_writable _ _ _ k.2 _ _ e₂).2⟩

/-- Every number of a location as read is below `2^32`. -/
theorem readLocation_writable (ts : List Token) :
    ReadsWritable readLocation Location.InLimits ts := by
  intro hw l r h
  unfold readLocation at h
  split at h
  · bind_step h with ⟨⟨l', a⟩, e₁, h⟩
    cases h
    exact readRange_writable _ _ hw.tail _ _ e₁
  · cases h
    exact ⟨by simp [Location.InLimits, Location.numbers, Location.refs], hw.tail⟩
  · split at h
    · bind_step h with ⟨⟨_, a⟩, e₁, h⟩
      bind_step h with ⟨⟨l', b⟩, e₂, h⟩
      cases h
      exact readLocArgs_writable _ _ (expect_writable _ _ _ hw.tail _ _ e₁).2 _ _ e₂
    · cases h
  · exact absurd h fail_ne_ok

/-- Every entry of the location table as read is within the limits: its
reference comes from a location reference token. -/
theorem readLocEntries_writable : ∀ ts, ReadsWritable readLocEntries LocTable.InLimits ts := by
  intro ts
  induction ts using readLocEntries.induct with
  | case1 n pos rest ih =>
    intro hw es r h
    rw [readLocEntries.eq_1] at h
    bind_step h with ⟨⟨_, a, ha⟩, e₁, h⟩
    bind_step h with ⟨⟨l, b, hb⟩, e₂, h⟩
    bind_step h with ⟨⟨es', c, hc⟩, e₃, h⟩
    cases h
    have w₁ := (expect_writable _ _ _ hw.tail _ _ e₁).2
    obtain ⟨k₂, w₂⟩ := readLocation_writable _ w₁ _ _ e₂
    obtain ⟨k₃, w₃⟩ := ih a ha b hb w₂ _ _ e₃
    exact ⟨fun e he => (List.mem_cons.mp he).elim (· ▸ ⟨hw.locRef, k₂⟩) (k₃ e), w₃⟩
  | case2 ts hne =>
    intro hw es r h
    rw [readLocEntries.eq_2 _ hne] at h
    cases h
    exact ⟨by simp [LocTable.InLimits], hw⟩

/-- The location table as read is within the limits. -/
theorem readLocs_writable (ts : List Token) : ReadsWritable readLocs LocTable.InLimits ts := by
  intro hw es r h
  unfold readLocs at h
  bind_step h with ⟨⟨_, a⟩, e₁, h⟩
  bind_step h with ⟨⟨_, b⟩, e₂, h⟩
  bind_step h with ⟨⟨es', c⟩, e₃, h⟩
  bind_step h with ⟨⟨_, d⟩, e₄, h⟩
  cases h
  have w₁ := (keyword_writable _ _ hw _ _ e₁).2
  have w₂ := (expect_writable _ _ _ w₁ _ _ e₂).2
  obtain ⟨k₃, w₃⟩ := readLocEntries_writable _ w₂ _ _ e₃
  exact ⟨k₃, (expect_writable _ _ _ w₃ _ _ e₄).2⟩

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

/-- The grammar step: on tokens that can be written, `readModule` gives a
tree that can be written. -/
theorem readModule_writable {ts : List Token} {s : SModule} (h : readModule ts = .ok s)
    (hw : TokensWritable ts) : s.Writable := by
  unfold readModule at h
  bind_step h with ⟨⟨ns, a₀⟩, e₀, h⟩
  obtain ⟨k₀, w₀⟩ := readDialects_writable _ hw _ _ e₀
  bind_step h with ⟨⟨items, a⟩, e₁, h⟩
  obtain ⟨k₁, w₁⟩ := readItems_writable _ _ w₀ _ _ e₁
  dsimp only at h
  split at h
  · rename_i heq
    bind_step h with ⟨⟨locs, b⟩, e₂, h⟩
    bind_step h with ⟨⟨_, c⟩, e₃, h⟩
    cases h
    exact ⟨k₀, k₁, (readLocs_writable _ (heq ▸ w₁) _ _ e₂).1⟩
  · exact absurd h fail_ne_ok

end Fir.Text
