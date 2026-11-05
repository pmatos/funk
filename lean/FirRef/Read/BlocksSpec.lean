import FirRef.Read.Heads

/-!
The spec's readers of blocks, ops and regions, one equation per case, with
`U` pushed inside: each says what the reader returns in terms of what the
readers it calls return, with the tokens after each as a plain list. The
blocks machine's proof unfolds the spec through these equations. Each is
proved by unfolding the reader once and moving `U` into its binds
(`U_bind`, `bind_U`).
-/

namespace FirRef

open Fir Fir.Text Cursor

theorem U_readBlocks_label (l : Name) (p : TextPos) (rest : List Token) :
    U (readBlocks (⟨.label l, p⟩ :: rest)) = (do
      let (params, r₂) ← blockHeadS rest
      let (ops, r₃) ← U (readOps r₂)
      let (bs, r₄) ← U (readBlocks r₃)
      pure (⟨l, params, ops⟩ :: bs, r₄)) := by
  rw [readBlocks.eq_def]
  simp only [blockHeadS]
  U_norm
  split <;> simp

theorem U_readBlocks_nil {ts : List Token} (h : ∀ l p rest, ts ≠ ⟨.label l, p⟩ :: rest) :
    U (readBlocks ts) = .ok ([], ts) := by
  rw [readBlocks.eq_def]
  split
  · rename_i l p rest
    exact absurd rfl (h l p rest)
  · rfl

theorem U_readOps_value (n : Name) (p : TextPos) (rest : List Token) :
    U (readOps (⟨.value n, p⟩ :: rest)) = (do
      let (o, r) ← U (readOpWithResults n p rest)
      let (os, r') ← U (readOps r)
      pure (o :: os, r')) := by
  rw [readOps.eq_def]
  U_norm

theorem U_readOps_word (w : String) (p : TextPos) (rest : List Token) :
    U (readOps (⟨.word w, p⟩ :: rest)) = (do
      let (o, r) ← U (readOpBody [] w p rest)
      let (os, r') ← U (readOps r)
      pure (o :: os, r')) := by
  rw [readOps.eq_def]
  U_norm

theorem U_readOps_nil {ts : List Token} (hv : ∀ n p rest, ts ≠ ⟨.value n, p⟩ :: rest)
    (hw : ∀ w p rest, ts ≠ ⟨.word w, p⟩ :: rest) : U (readOps ts) = .ok ([], ts) := by
  rw [readOps.eq_def]
  split
  · rename_i n p rest
    exact absurd rfl (hv n p rest)
  · rename_i w p rest
    exact absurd rfl (hw w p rest)
  · rfl

theorem U_readOpBody (results : List SDef) (name : String) (namePos : TextPos)
    (ts : List Token) :
    U (readOpBody results name namePos ts) = (do
      let (hd, r₂) ← opBodyHeadS results name namePos ts
      let (regions, r₃) ← U (readRegions r₂)
      let (loc, r₄) ← U (readOpLoc r₃)
      pure (hd.op regions loc, r₄)) := by
  rw [readOpBody.eq_def]
  simp only [opBodyHeadS, OpHead.op]
  U_norm

theorem U_readOpWithResults (n : Name) (p : TextPos) (ts : List Token) :
    U (readOpWithResults n p ts) = (do
      let (hd, r₂) ← opWithResultsHeadS n p ts
      let (regions, r₃) ← U (readRegions r₂)
      let (loc, r₄) ← U (readOpLoc r₃)
      pure (hd.op regions loc, r₄)) := by
  rw [readOpWithResults.eq_def]
  simp only [opWithResultsHeadS]
  U_norm
  congr 1
  funext d
  congr 1
  funext ds
  split
  · rename_i q w wp rest he
    simp only [he]
    rw [U_bind_pure, U_readOpBody]
    U_norm
  · rename_i q rest hne he
    simp only [he]
    simp only [U_fail, fail_bind]
  · rename_i hn hn'
    split
    · rename_i he
      exact absurd he (hn _ _ _ _)
    · rename_i he
      exact absurd he (hn' _ _)
    · simp only [U_fail, fail_bind]

theorem U_readRegions_lbrace (p : TextPos) (rest : List Token) :
    U (readRegions (⟨.lbrace, p⟩ :: rest)) = (do
      let (bs, r₁) ← U (readBlocks rest)
      let ((), r₂) ← U (expect .rbrace "a block or } to close the region" r₁)
      let (rs, r₃) ← U (readRegions r₂)
      pure (⟨bs⟩ :: rs, r₃)) := by
  rw [readRegions.eq_def]
  U_norm

theorem U_readRegions_nil {ts : List Token} (h : ∀ p rest, ts ≠ ⟨.lbrace, p⟩ :: rest) :
    U (readRegions ts) = .ok ([], ts) := by
  rw [readRegions.eq_def]
  split
  · rename_i p rest
    exact absurd rfl (h p rest)
  · rfl

end FirRef
