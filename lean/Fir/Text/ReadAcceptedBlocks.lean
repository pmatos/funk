import Fir.Text.ReadAccepted

/-!
# Ops, blocks and regions as read

On tokens that can be written, the readers of blocks, ops and regions give
blocks, ops and regions that can be written, at any depth. An op's name
comes from a word token and its results from `readDefs`; its attributes,
successors and location reference come from the readers of the previous
section, and its regions from `readRegions`. A block's label comes from a
label token.

The five readers call one another, to any depth. They are proved together
by their functional induction principle, `readBlocks.induct`, which Lean
derives from the readers' own recursion. Each case of the principle is one
reader on one shape of tokens, and takes what the readers it calls do on
the tokens left to them as hypotheses: the structure that
ADR-2026-11-03-0028 records for the round trip's lemmas. No case unfolds a
reader that it calls.
-/

namespace Fir.Text

/-- A list of attributes each of which can be written can be written. -/
theorem Attr.allWritable_of_forall :
    ∀ {as : List Attr}, (∀ a ∈ as, a.Writable) → Attr.AllWritable as
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (.head _), Attr.allWritable_of_forall fun a ha => h a (.tail _ ha)⟩

/-- On tokens that can be written, the readers of blocks, ops and regions
give blocks, ops and regions that can be written. Each case is a reader on
one shape of tokens. -/
theorem readBlocks_writable : ∀ ts, ReadsWritable readBlocks SBlock.WritableList ts := by
  intro ts
  induction ts using readBlocks.induct
    (motive2 := ReadsWritable readOps SOp.WritableList)
    (motive3 := fun results name namePos ts => (∀ x ∈ results, x.Writable) → isWord name →
      ReadsWritable (readOpBody results name namePos) SOp.Writable ts)
    (motive4 := ReadsWritable readRegions SRegion.WritableList)
    (motive5 := fun n p ts => isName n → ReadsWritable (readOpWithResults n p) SOp.Writable ts) with
  | case1 l pos rest ihops ihbs => -- `readBlocks`: a block, then the blocks after it
    intro hw bs r h
    rw [readBlocks.eq_def] at h
    simp only at h
    bind_step h with ⟨⟨params, r₁, h₁⟩, e₁, h⟩
    have k₁ : (∀ x ∈ params, x.Writable) ∧ TokensWritable r₁ := by
      split at e₁
      · bind_step e₁ with ⟨⟨ps, a⟩, f₁, e₁⟩
        bind_step e₁ with ⟨⟨_, b⟩, f₂, e₁⟩
        cases e₁
        obtain ⟨k, w₁⟩ := readDefs_writable _ hw.tail.tail _ _ f₁
        exact ⟨k, (expect_writable _ _ _ w₁ _ _ f₂).2⟩
      · cases e₁
        exact ⟨by simp, hw.tail⟩
    bind_step h with ⟨⟨_, r₂, h₂⟩, e₂, h⟩
    bind_step h with ⟨⟨ops, r₃, h₃⟩, e₃, h⟩
    bind_step h with ⟨⟨bs', r₄, h₄⟩, e₄, h⟩
    cases h
    have w₂ := (expect_writable _ _ _ k₁.2 _ _ e₂).2
    obtain ⟨k₃, w₃⟩ := ihops r₁ h₁ r₂ h₂ w₂ _ _ e₃
    obtain ⟨k₄, w₄⟩ := ihbs r₁ h₁ r₂ h₂ r₃ h₃ w₃ _ _ e₄
    exact ⟨⟨hw.label, k₁.1, k₃, k₄⟩, w₄⟩
  | case2 ts hne => -- `readBlocks`: no block
    intro hw bs r h
    rw [readBlocks.eq_3 _ hne] at h
    cases h
    exact ⟨trivial, hw⟩
  | case3 n p rest ih ihops => -- `readOps`: an op with results
    intro hw os r h
    rw [readOps.eq_1] at h
    bind_step h with ⟨⟨o, r₁, h₁⟩, e₁, h⟩
    bind_step h with ⟨⟨os', r₂, h₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := ih hw.value hw.tail _ _ e₁
    obtain ⟨k₂, w₂⟩ := ihops r₁ h₁ w₁ _ _ e₂
    exact ⟨⟨k₁, k₂⟩, w₂⟩
  | case4 w p rest ih ihops => -- `readOps`: an op without results
    intro hw os r h
    rw [readOps.eq_2] at h
    bind_step h with ⟨⟨o, r₁, h₁⟩, e₁, h⟩
    bind_step h with ⟨⟨os', r₂, h₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := ih (by simp) hw.word hw.tail _ _ e₁
    obtain ⟨k₂, w₂⟩ := ihops r₁ h₁ w₁ _ _ e₂
    exact ⟨⟨k₁, k₂⟩, w₂⟩
  | case5 ts h₁ h₂ => -- `readOps`: no op
    intro hw os r h
    rw [readOps.eq_3 _ h₁ h₂] at h
    cases h
    exact ⟨trivial, hw⟩
  | case6 results name namePos ts ihregs => -- `readOpBody`
    rename_i hres hname
    intro hw o r h
    rw [readOpBody] at h
    bind_step h with ⟨⟨attrs, r₁, h₁⟩, e₁, h⟩
    bind_step h with ⟨⟨⟨operands, succs⟩, r₂, h₂⟩, e₂, h⟩
    bind_step h with ⟨⟨regions, r₃, h₃⟩, e₃, h⟩
    bind_step h with ⟨⟨loc, r₄, h₄⟩, e₄, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readAttrs_writable _ hw _ _ e₁
    obtain ⟨k₂, w₂⟩ := readOperands_writable _ w₁ _ _ e₂
    obtain ⟨k₃, w₃⟩ := ihregs r₁ h₁ r₂ h₂ w₂ _ _ e₃
    obtain ⟨k₄, w₄⟩ := readOpLoc_writable _ w₃ _ _ e₄
    refine ⟨⟨hres, hname, Attr.allWritable_of_forall ?_, k₂, k₃, k₄⟩, w₄⟩
    simpa using k₁
  | case7 pos rest ihbs ihregs => -- `readRegions`: a region, then the regions after it
    intro hw rs r h
    rw [readRegions.eq_1] at h
    bind_step h with ⟨⟨bs, r₁, h₁⟩, e₁, h⟩
    bind_step h with ⟨⟨_, r₂, h₂⟩, e₂, h⟩
    bind_step h with ⟨⟨rs', r₃, h₃⟩, e₃, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := ihbs hw.tail _ _ e₁
    have w₂ := (expect_writable _ _ _ w₁ _ _ e₂).2
    obtain ⟨k₃, w₃⟩ := ihregs r₁ h₁ r₂ h₂ w₂ _ _ e₃
    exact ⟨⟨k₁, k₃⟩, w₃⟩
  | case8 ts hne => -- `readRegions`: no region
    intro hw rs r h
    rw [readRegions.eq_2 _ hne] at h
    cases h
    exact ⟨trivial, hw⟩
  | case9 n p ts ih => -- `readOpWithResults`
    rename_i hn
    intro hw o r h
    rw [readOpWithResults] at h
    bind_step h with ⟨⟨x, r₁, h₁⟩, e₁, h⟩
    bind_step h with ⟨⟨xs, r₂, h₂⟩, e₂, h⟩
    obtain ⟨⟨hx, k₁⟩, w₁⟩ := readDefType_writable _ _ _ hw _ _ e₁
    obtain ⟨k₂, w₂⟩ := readMore_writable readDef_writable _ w₁ _ _ e₂
    dsimp only at h
    split at h
    · bind_step h with ⟨⟨o', r₃, h₃⟩, e₃, h⟩
      cases h
      have hres : ∀ y ∈ x :: xs, y.Writable := fun y hy =>
        (List.mem_cons.mp hy).elim (· ▸ ⟨hx ▸ hn, k₁⟩) (k₂ y)
      exact ih x r₁ h₁ xs _ h₂ _ _ _ _ rfl hres w₂.tail.word w₂.tail.tail _ _ e₃
    · exact absurd h fail_ne_ok
    · exact absurd h fail_ne_ok

end Fir.Text
