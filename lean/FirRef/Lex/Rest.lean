import FirRef.Lex.Next

/-!
One step of the spec's `lexFrom`, over positions, is `nextTokP`:
`lexFrom_eq` says that `lexFrom` from a position is `nextTokP` there, then
`lexFrom` again from the position after the token it read. `lexFrom_token`
is the step that reads a token with `lexTokenP`, the spec's `lexToken` over
positions (`lexTokenP_agree`).
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

theorem peekP_of_chars {i : s.Pos} {c : Char} {cs : List Char} (h : chars i = c :: cs) :
    ∃ j, peekP i = some (c, j) ∧ chars j = cs := by
  unfold peekP
  split
  · rename_i he
    rw [he, chars_endPos] at h
    cases h
  · rename_i hne
    rw [chars_next hne] at h
    simp only [List.cons.injEq] at h
    exact ⟨_, by rw [h.1], h.2⟩

/-- `lexTokenP` fails where `lexToken` fails, with the same error, and
otherwise reads the same token, with the characters after it from its
position. -/
theorem lexTokenP_agree (c : Char) (i : s.Pos) (p : TextPos) :
    (∃ e, lexTokenP c i p = .error e ∧ lexToken c (chars i) p = .error e) ∨
      (∃ t j q hr, lexTokenP c i p = .ok (t, j, q) ∧
        lexToken c (chars i) p = .ok (t, ⟨chars j, hr⟩, q)) := by
  have e := lexTokenP_eq c i p
  revert e
  rcases lexTokenP c i p with e₁ | ⟨t, j, q⟩ <;>
    rcases lexToken c (chars i) p with e₂ | ⟨t', ⟨r, hr⟩, q'⟩ <;>
    simp only [okExceptMap, errorExceptMap, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq,
      reduceCtorEq, false_implies]
  · intro he
    exact .inl ⟨e₁, rfl, by rw [he]⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact .inr ⟨t, j, q, hr, by simp, by simp⟩

theorem lexTokenP_le {c : Char} {i j : s.Pos} {p q : TextPos} {t : Tok}
    (h : lexTokenP c i p = .ok (t, j, q)) : (chars j).length ≤ (chars i).length := by
  rcases lexTokenP_agree c i p with ⟨e, hx, _⟩ | ⟨t', j', q', hr, hx, _⟩
  · rw [hx] at h
    cases h
  · rw [hx] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hr

/-- `lexFrom` on a token that starts with `c`, which is not whitespace and
does not start a comment: `lexTokenP` reads it. -/
theorem lexFrom_token {c : Char} {i₁ : s.Pos} (p : TextPos) (acc : List Token)
    (hws : ¬(c = ' ' ∨ c = '\t')) (hnl : ¬c = '\n')
    (hs : ∀ rest, c = '/' → chars i₁ = '/' :: rest → False) :
    lexFrom (c :: chars i₁) p acc = match lexTokenP c i₁ p with
      | .ok (t, j, q) => lexFrom (chars j) q (⟨t, p⟩ :: acc)
      | .error e => .error e := by
  rw [lexFrom.eq_6 _ _ _ _ (fun e => hws (.inl e)) (fun e => hws (.inr e)) hnl hs]
  rcases lexTokenP_agree c i₁ p with ⟨e, hx, hy⟩ | ⟨t, j, q, hr, hx, hy⟩
  · rw [hx, hy]
    rfl
  · rw [hx, hy]
    rfl

theorem lexFrom_eq (i : s.Pos) (p : TextPos) (acc : List Token) :
    lexFrom (chars i) p acc = match nextTokP i p with
      | .error e => .error e
      | .ok (t, none) => .ok (t :: acc).reverse
      | .ok (t, some (j, q)) => lexFrom (chars j) q (t :: acc) := by
  fun_induction nextTokP i p with
  | case1 i p h =>
    rw [chars_of_peekP_none h, lexFrom]
    try rfl
  | case2 i p c i₁ h hc ih =>
    rw [← ih, chars_of_peekP h]
    rcases hc with rfl | rfl <;> rw [lexFrom]
  | case3 i p i₁ h hc ih =>
    rw [← ih, chars_of_peekP h, lexFrom]
  | case4 i p i₁ i₂ h₁ c' n hc h =>
    rw [chars_of_peekP h, chars_of_peekP h₁, lexFrom]
    simp only [commentP_inl hc]
    try rfl
  | case5 i p i₁ i₂ h₁ n j hc h hws hnl ih =>
    obtain ⟨hfd, rfl, rfl⟩ := commentP_inr hc
    rw [← ih, chars_of_peekP h, chars_of_peekP h₁, lexFrom]
    simp only [hfd, chars_skipWhileP, Nat.zero_add]
  | case6 i p c i₁ h hws hnl i₂ h₁ hs t j q hx | case7 i p c i₁ h hws hnl i₂ h₁ hs e hx =>
    rw [chars_of_peekP h, lexFrom_token p acc hws hnl (fun _ e _ => hs e), hx]
    try rfl
  | case8 i p c i₁ h hws hnl t j q hx hn | case9 i p c i₁ h hws hnl e hx hn =>
    rw [chars_of_peekP h, lexFrom_token p acc hws hnl (fun _ _ he => by
      obtain ⟨j₀, hj, _⟩ := peekP_of_chars he
      exact hn j₀ hj), hx]
    try rfl

end FirRef
