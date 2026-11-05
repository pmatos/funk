import FirRef.Read.ItemHead

/-!
`itemHeadC` reads an item's head on a cursor, as the spec's `readItem`
does up to the `{` of the body (`itemHeadS`).
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- `itemParamsS`, on a cursor. -/
def itemParamsC (s : σ) : Except ParseError (List SDef × σ) :=
  match uncons s with
  | some (⟨.rparen, _⟩, _) => .ok ([], s)
  | _ => readDefsC s

theorem itemParamsC_eq (s : σ) : V (itemParamsC s) = itemParamsS (view s) := by
  unfold itemParamsC itemParamsS
  split
  · rename_i p s₁ h
    rw [view_of_uncons h]
    simp [view_of_uncons h]
    rfl
  · rename_i hn
    split
    · rename_i p rest he
      exact absurd he (not_head hn p rest)
    · exact readDefsC_eq s

theorem itemParamsC_le {s s' : σ} {ps : List SDef} (h : itemParamsC s = .ok (ps, s')) :
    (view s').length ≤ (view s).length := by
  unfold itemParamsC at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ Nat.le_refl _
  · exact readDefsC_le h

theorem readTypeC_le' (s : σ) (a : Attr × TextPos) (s' : σ) (h : readTypeC s = .ok (a, s')) :
    (view s').length ≤ (view s).length :=
  readTypeC_le h

/-- `itemResultsS`, on a cursor. -/
def itemResultsC (s : σ) : Except ParseError (List (Attr × TextPos) × σ) :=
  match uncons s with
  | some (⟨.arrow, _⟩, s₁) =>
    match readTypeC s₁ with
    | .ok (t, s₂) =>
      match readMoreC readTypeC readTypeC_le' s₂ [] with
      | .ok (more, s₃) => .ok (t :: more, s₃)
      | .error e => .error e
    | .error e => .error e
  | _ => .ok ([], s)

theorem itemResultsC_eq (s : σ) : V (itemResultsC s) = itemResultsS (view s) := by
  unfold itemResultsC itemResultsS
  split
  · rename_i p s₁ h
    rw [view_of_uncons h]
    simp only
    rcases agree (readTypeC_eq s₁) with ⟨e, hx, hy⟩ | ⟨t, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [U_ok, okBind]
      rcases agree_map (f := fun q => ([].reverse ++ q))
        (readMoreC_eq readTypeC readTypeC_le' readType readTypeC_eq s₂ []) with
        ⟨e, hx', hy'⟩ | ⟨more, s₃, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        rfl
  · rename_i hn
    split
    · rename_i p rest he
      exact absurd he (not_head hn p rest)
    · rfl

theorem itemResultsC_le {s s' : σ} {rs : List (Attr × TextPos)}
    (h : itemResultsC s = .ok (rs, s')) : (view s').length ≤ (view s).length := by
  unfold itemResultsC at h
  split at h
  · rename_i p s₁ hs
    split at h
    · rename_i t s₂ h₂
      split at h
      · rename_i more s₃ h₃
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        have := readMoreC_le h₃
        have := readTypeC_le h₂
        have := length_lt hs
        omega
      · cases h
    · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ Nat.le_refl _

/-- `itemHeadS`, on a cursor. -/
def itemHeadC (kind : String) (p : TextPos) (s : σ) : Except ParseError (ItemHead × σ) :=
  match uncons s with
  | some (⟨.sym name, _⟩, s₁) => do
    let ((), s₂) ← expectC .lparen "( and the item's parameters" s₁
    let (params, s₃) ← itemParamsC s₂
    let ((), s₄) ← expectC .rparen ")" s₃
    let (results, s₅) ← itemResultsC s₄
    let (attrs, s₆) ← readAttrsC s₅ []
    let ((), s₇) ← expectC .lbrace "{ and the item's body" s₆
    pure (⟨kind, p, name, params, results, attrs⟩, s₇)
  | _ => failC s "the item's symbol"

theorem itemHeadC_eq (kind : String) (p : TextPos) (s : σ) :
    V (itemHeadC kind p s) = itemHeadS kind p (view s) := by
  unfold itemHeadC itemHeadS
  split
  · rename_i name q s₁ h
    rw [view_of_uncons h]
    simp only
    rcases agree (expectC_eq .lparen "( and the item's parameters" s₁) with
      ⟨e, hx, hy⟩ | ⟨⟨⟩, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [U_ok, okBind]
      have e₂ := itemParamsC_eq s₂
      rcases hx₂ : itemParamsC s₂ with e | ⟨ps, s₃⟩ <;> rw [hx₂] at e₂ <;> rw [← e₂]
      · rfl
      · simp only [V_ok, okBind]
        rcases agree (expectC_eq .rparen ")" s₃) with
          ⟨e, hx', hy'⟩ | ⟨⟨⟩, s₄, r', hr', hx', hy', hv'⟩
        · rw [hx', hy']; rfl
        · rw [hx', hy']
          subst hv'
          simp only [U_ok, okBind]
          have e₄ := itemResultsC_eq s₄
          rcases hx₄ : itemResultsC s₄ with e | ⟨rs, s₅⟩ <;> rw [hx₄] at e₄ <;> rw [← e₄]
          · rfl
          · simp only [V_ok, okBind]
            rcases agree_map (f := fun q => ([].reverse ++ q)) (readAttrsC_eq s₅ []) with
              ⟨e, hx'', hy''⟩ | ⟨attrs, s₆, r'', hr'', hx'', hy'', hv''⟩
            · rw [hx'', hy'']; rfl
            · rw [hx'', hy'']
              subst hv''
              simp only [U_ok, okBind, List.reverse_nil, List.nil_append]
              rcases agree (expectC_eq .lbrace "{ and the item's body" s₆) with
                ⟨e, hx₃, hy₃⟩ | ⟨⟨⟩, s₇, r₃, hr₃, hx₃, hy₃, hv₃⟩
              · rw [hx₃, hy₃]; rfl
              · rw [hx₃, hy₃]
                subst hv₃
                rfl
  · rename_i hn
    rw [failC_eq, V_fail]
    split
    · rename_i name q rest he
      exact absurd he (not_head (hn name) q rest)
    · rfl

theorem itemHeadC_lt {kind : String} {p : TextPos} {s s' : σ} {hd : ItemHead}
    (h : itemHeadC kind p s = .ok (hd, s')) : (view s').length < (view s).length := by
  unfold itemHeadC at h
  split at h
  · rename_i name q s₁ hs
    have := length_lt hs
    rcases h₂ : expectC .lparen "( and the item's parameters" s₁ with e | ⟨⟨⟩, s₂⟩ <;>
      rw [h₂] at h <;> simp only [errorBind, okBind, reduceCtorEq] at h
    have := expectC_lt h₂
    rcases h₃ : itemParamsC s₂ with e | ⟨ps, s₃⟩ <;>
      rw [h₃] at h <;> simp only [errorBind, okBind, reduceCtorEq] at h
    have := itemParamsC_le h₃
    rcases h₄ : expectC .rparen ")" s₃ with e | ⟨⟨⟩, s₄⟩ <;>
      rw [h₄] at h <;> simp only [errorBind, okBind, reduceCtorEq] at h
    have := expectC_lt h₄
    rcases h₅ : itemResultsC s₄ with e | ⟨rs, s₅⟩ <;>
      rw [h₅] at h <;> simp only [errorBind, okBind, reduceCtorEq] at h
    have := itemResultsC_le h₅
    rcases h₆ : readAttrsC s₅ [] with e | ⟨attrs, s₆⟩ <;>
      rw [h₆] at h <;> simp only [errorBind, okBind, reduceCtorEq] at h
    have := readAttrsC_le h₆
    rcases h₇ : expectC .lbrace "{ and the item's body" s₆ with e | ⟨⟨⟩, s₇⟩ <;>
      rw [h₇] at h <;> simp only [errorBind, okBind, reduceCtorEq] at h
    have := expectC_lt h₇
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    omega
  · rw [failC_eq] at h
    cases hv : view s <;> rw [hv] at h <;> cases h

end FirRef
