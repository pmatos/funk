import FirRef.Read.Module

/-!
The spec's `Text.readModule` accepts only a list of tokens that holds
`eof`, since a module ends with `expect .eof`. `readModule_ok_eof` proves it
from `readModuleC_eq` alone, with no new fact about the spec's readers:
`IdxCursor` reads a fixed list by index, so every token it gives is in the
list, and `readModuleC` accepts only after it takes an `eof` from its
cursor (`readModuleC_ok_eof`).
-/

namespace FirRef

open Fir Fir.Text Cursor

/-- A cursor over the list `P`, at the index `k`. Only proofs use it. -/
structure IdxCursor (P : List Token) where
  k : Nat

/-- The token at the cursor's index, and the cursor after it. -/
def IdxCursor.uncons {P : List Token} (c : IdxCursor P) : Option (Token × IdxCursor P) :=
  match P[c.k]? with
  | none => none
  | some t => some (t, ⟨c.k + 1⟩)

instance (P : List Token) : Cursor (IdxCursor P) where
  uncons := IdxCursor.uncons
  view c := P.drop c.k
  view_uncons c := by
    rcases c with ⟨k⟩
    simp only [IdxCursor.uncons]
    rcases h : P[k]? with _ | t
    · simp only
      rw [List.getElem?_eq_none_iff] at h
      exact List.drop_eq_nil_of_le h
    · simp only
      obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
      exact List.drop_eq_getElem_cons hk

theorem IdxCursor.mem_of_uncons {P : List Token} {c c' : IdxCursor P} {t : Token}
    (h : Cursor.uncons c = some (t, c')) : t ∈ P := by
  change IdxCursor.uncons c = some (t, c') at h
  unfold IdxCursor.uncons at h
  split at h
  · cases h
  · rename_i u hu
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact List.mem_iff_getElem?.2 ⟨_, hu⟩

section
variable {σ : Type} [Cursor σ]

theorem expectC_ok {tok : Tok} {msg : String} {s : σ} {r : Unit × σ}
    (h : expectC tok msg s = .ok r) : ∃ t s', uncons s = some (t, s') ∧ t.tok = tok := by
  unfold expectC at h
  split at h
  · rename_i t s₁ hu
    split at h
    · rename_i ht
      exact ⟨t, s₁, hu, ht⟩
    · simp [fail] at h
  · simp [fail] at h

/-- `readModuleC` accepts only after it takes an `eof` from some cursor. -/
theorem readModuleC_ok_eof {s : σ} {m : SModule} (h : readModuleC s = .ok m) :
    ∃ (s₂ : σ) (t : Token) (s₃ : σ), uncons s₂ = some (t, s₃) ∧ t.tok = .eof := by
  unfold readModuleC at h
  rcases h0 : readDialectsC s with e | ⟨ns, s₀'⟩ <;> rw [h0] at h
  · cases h
  dsimp only at h
  rcases h0' : readLayoutC s₀' with e | ⟨layout, s₀⟩ <;> rw [h0'] at h
  · cases h
  dsimp only at h
  rcases h1 : readItemsC s₀ with e | ⟨items, s₁⟩ <;> rw [h1] at h
  · cases h
  · dsimp only at h
    split at h
    · rcases h2 : readLocsC s₁ with e | ⟨locs, s₂⟩ <;> rw [h2] at h
      · cases h
      · dsimp only at h
        rcases h3 : expectC .eof "the end of the text after the location table" s₂ with e | r <;>
          rw [h3] at h
        · cases h
        · obtain ⟨t, s₃, hu, ht⟩ := expectC_ok h3
          exact ⟨s₂, t, s₃, hu, ht⟩
    · unfold failC at h
      split at h <;> simp [fail] at h
end

/-- The spec's `readModule` accepts only a list that holds `eof`. -/
theorem readModule_ok_eof {P : List Token} {m : SModule} (h : Text.readModule P = .ok m) :
    ∃ t ∈ P, t.tok = .eof := by
  have h' : readModuleC (⟨0⟩ : IdxCursor P) = .ok m := by
    rw [readModuleC_eq]
    exact h
  obtain ⟨s₂, t, s₃, hu, ht⟩ := readModuleC_ok_eof h'
  exact ⟨t, IdxCursor.mem_of_uncons hu, ht⟩

end FirRef
