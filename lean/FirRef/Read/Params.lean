import FirRef.Read.Lists

/-!
The readers of an item's parameters and results, on a cursor: each a
definition or a type, then its attributes, and the parameters may end in
`...`. The loop over further parameters keeps those read so far, last
first, so its only call to itself is a tail call.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- `readParam`, on a cursor. -/
def readParamC (s : σ) : Except ParseError ((SDef × List (Attr × TextPos)) × σ) :=
  match readDefC s with
  | .ok (d, s₁) =>
    match readAttrsC s₁ [] with
    | .ok (as, s₂) => .ok ((d, as), s₂)
    | .error e => .error e
  | .error e => .error e

theorem readParamC_eq (s : σ) : V (readParamC s) = U (readParam (view s)) := by
  unfold readParamC readParam
  rcases agree (readDefC_eq s) with ⟨e, hx, hy⟩ | ⟨d, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [okBind]
    rcases agree_map (f := fun q => ([].reverse ++ q)) (readAttrsC_eq s₁ []) with
      ⟨e, hx', hy'⟩ | ⟨as, s₂, r', hr', hx', hy', hv'⟩
    · rw [hx', hy']; rfl
    · rw [hx', hy']
      subst hv'
      rfl

theorem readParamC_le {s s' : σ} {x : SDef × List (Attr × TextPos)}
    (h : readParamC s = .ok (x, s')) : (view s').length ≤ (view s).length :=
  length_le (readParamC_eq s) rfl h

/-- `readMoreParams`, on a cursor: the parameters read so far are `acc`,
last first. -/
def readMoreParamsC (s : σ) (acc : List (SDef × List (Attr × TextPos))) :
    Except ParseError ((List (SDef × List (Attr × TextPos)) × Option TextPos) × σ) :=
  match _h : uncons s with
  | some (⟨.comma, _⟩, s₁) =>
    match uncons s₁ with
    | some (⟨.ellipsis, p⟩, s₂) => .ok ((acc.reverse, some p), s₂)
    | _ =>
      match _hi : readParamC s₁ with
      | .ok (x, s₂) => readMoreParamsC s₂ (x :: acc)
      | .error e => .error e
  | _ => .ok ((acc.reverse, none), s)
termination_by (view s).length
decreasing_by exact Nat.lt_of_le_of_lt (readParamC_le _hi) (length_lt _h)

theorem readMoreParamsC_eq (s : σ) (acc : List (SDef × List (Attr × TextPos))) :
    V (readMoreParamsC s acc) = (U (readMoreParams (view s))).map
      fun ((xs, v), r) => ((acc.reverse ++ xs, v), r) := by
  fun_induction readMoreParamsC s acc with
  | case1 s acc q s₁ h p s₂ h₁ =>
    rw [view_of_uncons h, view_of_uncons h₁, readMoreParams.eq_1]
    simp [Except.map]
  | case2 s acc q s₁ h x s₂ hi hn ih =>
    have e := readParamC_eq s₁
    rw [hi, V_ok] at e
    rw [ih, view_of_uncons h, readMoreParams.eq_2 _ _ (fun p rest he => not_head hn p rest he)]
    revert e
    rcases readParam (view s₁) with e | ⟨y, r, hr⟩
    · simp
    · simp only [U_ok, Except.ok.injEq, Prod.mk.injEq, okBind, and_imp]
      intro hy hr'
      subst hy hr'
      rcases readMoreParams (view s₂) with e | ⟨⟨xs, v⟩, r', hr''⟩ <;> simp [Except.map]
  | case3 s acc q s₁ h e he hn =>
    have e' := readParamC_eq s₁
    rw [he, V_error] at e'
    rw [view_of_uncons h, readMoreParams.eq_2 _ _ (fun p rest he => not_head hn p rest he)]
    revert e'
    rcases readParam (view s₁) with e | ⟨y, r, hr⟩ <;> simp [Except.map]
  | case4 s acc hn =>
    rw [readMoreParams.eq_3 _ (fun q p rest he => not_head hn q _ he)
      (fun q rest he => not_head hn q rest he)]
    simp [Except.map]

theorem readMoreParamsC_le {s s' : σ} {acc : List (SDef × List (Attr × TextPos))}
    {x : List (SDef × List (Attr × TextPos)) × Option TextPos}
    (h : readMoreParamsC s acc = .ok (x, s')) : (view s').length ≤ (view s).length := by
  fun_induction readMoreParamsC s acc with
  | case1 s acc q s₁ h₀ p s₂ h₁ =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    have := length_lt h₀
    have := length_lt h₁
    omega
  | case2 s acc q s₁ h₀ y s₂ hi hn ih =>
    exact Nat.le_trans (ih h) (Nat.le_of_lt (Nat.lt_of_le_of_lt (readParamC_le hi) (length_lt h₀)))
  | case3 => cases h
  | case4 =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ Nat.le_refl _

/-- `readParams`, on a cursor. -/
def readParamsC (s : σ) :
    Except ParseError ((List (SDef × List (Attr × TextPos)) × Option TextPos) × σ) :=
  match uncons s with
  | some (⟨.ellipsis, p⟩, s₁) => .ok (([], some p), s₁)
  | _ =>
    match readParamC s with
    | .ok (x, s₁) => readMoreParamsC s₁ [x]
    | .error e => .error e

theorem readParamsC_eq (s : σ) : V (readParamsC s) = U (readParams (view s)) := by
  unfold readParamsC
  split
  · rename_i p s₁ h
    rw [view_of_uncons h, readParams.eq_1]
    rfl
  · rename_i hn
    rw [readParams.eq_2 _ (fun p rest he => not_head hn p rest he)]
    rcases agree (readParamC_eq s) with ⟨e, hx, hy⟩ | ⟨x, s₁, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [okBind]
      rw [readMoreParamsC_eq]
      rcases readMoreParams (view s₁) with e | ⟨⟨xs, v⟩, r', hr'⟩ <;> rfl

theorem readParamsC_le {s s' : σ} {x : List (SDef × List (Attr × TextPos)) × Option TextPos}
    (h : readParamsC s = .ok (x, s')) : (view s').length ≤ (view s).length :=
  length_le (readParamsC_eq s) rfl h

/-- `readResult`, on a cursor. -/
def readResultC (s : σ) : Except ParseError (((Attr × TextPos) × List (Attr × TextPos)) × σ) :=
  match readTypeC s with
  | .ok (t, s₁) =>
    match readAttrsC s₁ [] with
    | .ok (as, s₂) => .ok ((t, as), s₂)
    | .error e => .error e
  | .error e => .error e

theorem readResultC_eq (s : σ) : V (readResultC s) = U (readResult (view s)) := by
  unfold readResultC readResult
  rcases agree (readTypeC_eq s) with ⟨e, hx, hy⟩ | ⟨t, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [okBind]
    rcases agree_map (f := fun q => ([].reverse ++ q)) (readAttrsC_eq s₁ []) with
      ⟨e, hx', hy'⟩ | ⟨as, s₂, r', hr', hx', hy', hv'⟩
    · rw [hx', hy']; rfl
    · rw [hx', hy']
      subst hv'
      rfl

theorem readResultC_le (s : σ) (x : (Attr × TextPos) × List (Attr × TextPos)) (s' : σ)
    (h : readResultC s = .ok (x, s')) : (view s').length ≤ (view s).length :=
  length_le (readResultC_eq s) rfl h

end FirRef
