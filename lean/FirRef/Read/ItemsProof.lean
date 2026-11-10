import FirRef.Read.Items

/-!
`itemsLoop` reads what the spec's readers of items read, and fails where
they fail: `itemsLoop_eq`, by induction on the loop. `readItemsC` starts
the loop at the top of a module.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

theorem itemBodyS_blocks {s : σ} (hn : ∀ w q s', uncons s = some (⟨.word w, q⟩, s') → False) :
    itemBodyS (view s) = (do
      let (bs, r) ← U (readBlocks (view s))
      pure (SBody.blocks bs, r)) := by
  unfold itemBodyS
  split
  · rename_i w q tl he
    exact absurd he (not_head (hn w) q tl)
  · rfl

theorem itemBodyS_word {s s' : σ} {w : String} {q : TextPos}
    (h : uncons s = some (⟨.word w, q⟩, s')) :
    itemBodyS (view s) = (do
      let (ds, r) ← U (readDialects (view s))
      let (is, r') ← U (readItems false r)
      pure (SBody.items ds is, r')) := by
  rw [view_of_uncons h]
  rfl

/-- Unfolds `iRun` and `iFinish` and reduces binds on known results. -/
macro "i_norm" : tactic => `(tactic| simp only [iRun, iFinish, V_ok, V_error, okBind, errorBind,
  pure_bind, bind_assoc, List.reverse_nil, List.nil_append, List.append_nil, List.reverse_cons,
  List.append_assoc, List.singleton_append, List.cons_append])

theorem itemsLoop_eq (s : σ) (fs : List IFrame) : V (itemsLoop s fs) = iRun (view s) fs := by
  fun_induction itemsLoop s fs with
  | case1 s top done fs w₁ p s₁ h hd s₂ hh w pos snd hw ds s₃ hdd ih =>
    rw [ih]
    obtain ⟨hs, hn⟩ := nextItem_some h
    rw [view_of_uncons hs]
    simp only [iRun]
    rw [U_readItems_word top w₁ p (view s₁) hn, U_readItem, ← itemHeadC_eq, hh]
    i_norm
    rw [itemBodyS_word hw]
    i_norm
    rw [← readDialectsC_eq, hdd]
    i_norm
  | case2 s top done fs w₁ p s₁ h hd s₂ hh w pos snd hw e hdd =>
    obtain ⟨hs, hn⟩ := nextItem_some h
    rw [view_of_uncons hs]
    simp only [iRun]
    rw [U_readItems_word top w₁ p (view s₁) hn, U_readItem, ← itemHeadC_eq, hh]
    i_norm
    rw [itemBodyS_word hw]
    i_norm
    rw [← readDialectsC_eq, hdd]
    rfl
  | case3 s top done fs w p s₁ h hd s₂ hh bs s₃ hb s₄ he hn ih =>
    rw [ih]
    obtain ⟨hs, hn'⟩ := nextItem_some h
    rw [view_of_uncons hs]
    simp only [iRun]
    rw [U_readItems_word top w p (view s₁) hn', U_readItem, ← itemHeadC_eq, hh]
    i_norm
    rw [itemBodyS_blocks hn]
    i_norm
    rw [← readBlocksC_eq, hb]
    i_norm
    rw [← expectC_eq, he]
    i_norm
  | case4 s top done fs w p s₁ h hd s₂ hh bs s₃ hb e he hn =>
    obtain ⟨hs, hn'⟩ := nextItem_some h
    rw [view_of_uncons hs]
    simp only [iRun]
    rw [U_readItems_word top w p (view s₁) hn', U_readItem, ← itemHeadC_eq, hh]
    i_norm
    rw [itemBodyS_blocks hn]
    i_norm
    rw [← readBlocksC_eq, hb]
    i_norm
    rw [← expectC_eq, he]
    rfl
  | case5 s top done fs w p s₁ h hd s₂ hh e hb hn =>
    obtain ⟨hs, hn'⟩ := nextItem_some h
    rw [view_of_uncons hs]
    simp only [iRun]
    rw [U_readItems_word top w p (view s₁) hn', U_readItem, ← itemHeadC_eq, hh]
    i_norm
    rw [itemBodyS_blocks hn]
    i_norm
    rw [← readBlocksC_eq, hb]
    rfl
  | case6 s top done fs w p s₁ h e hh =>
    obtain ⟨hs, hn'⟩ := nextItem_some h
    rw [view_of_uncons hs]
    simp only [iRun]
    rw [U_readItems_word top w p (view s₁) hn', U_readItem, ← itemHeadC_eq, hh]
    rfl
  | case7 s top done h =>
    simp only [iRun]
    rw [U_readItems_none h]
    i_norm
  | case8 s top done h hd ds top' done' fs s₄ he ih =>
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    rw [ih]
    simp only [iRun]
    rw [U_readItems_none h]
    i_norm
    rw [← expectC_eq, he]
    i_norm
  | case9 s top done h hd ds top' done' fs e he =>
    simp only [iRun]
    rw [U_readItems_none h]
    i_norm
    rw [← expectC_eq, he]
    rfl
  | case10 s top done fs h =>
    simp only [iRun]
    rw [U_readItems_none h]
    i_norm
  | case11 s fs hn =>
    rcases fs with _ | ⟨_ | _, fs⟩ <;> first | rfl | exact absurd rfl (hn _ _ _)

/-- `readItems true`, on a cursor, with no stack per level. -/
def readItemsC (s : σ) : Except ParseError (List SItem × σ) := itemsLoop s [.items true []]

theorem readItemsC_eq (s : σ) : V (readItemsC s) = U (readItems true (view s)) := by
  rw [readItemsC, itemsLoop_eq]
  simp only [iRun, iFinish]
  rcases U (readItems true (view s)) with e | ⟨is, r⟩ <;> simp

end FirRef
