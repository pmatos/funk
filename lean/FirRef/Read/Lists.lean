import FirRef.Read.Attr

/-!
The readers of flat lists, on a cursor: definitions and successors. Each
spec reader recurses once per element; each reader here is a loop that
keeps the elements read so far, last first, so its only call to itself is
a tail call.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ] {α : Type}

/-- `readMore item`, on a cursor, with `item` a reader that leaves no more
tokens than it is given. -/
def readMoreC (item : σ → Except ParseError (α × σ))
    (hitem : ∀ s a s', item s = .ok (a, s') → (view s').length ≤ (view s).length)
    (s : σ) (acc : List α) : Except ParseError (List α × σ) :=
  match _h : uncons s with
  | some (⟨.comma, _⟩, s₁) =>
    match _hi : item s₁ with
    | .ok (x, s₂) => readMoreC item hitem s₂ (x :: acc)
    | .error e => .error e
  | _ => .ok (acc.reverse, s)
termination_by (view s).length
decreasing_by exact Nat.lt_of_le_of_lt (hitem _ _ _ _hi) (length_lt _h)

theorem readMoreC_eq (item : σ → Except ParseError (α × σ))
    (hitem : ∀ s a s', item s = .ok (a, s') → (view s').length ≤ (view s).length)
    (itemS : (ts : List Token) → Read α ts) (hsim : ∀ s, V (item s) = U (itemS (view s)))
    (s : σ) (acc : List α) :
    V (readMoreC item hitem s acc) =
      (U (readMore itemS (view s))).map fun (xs, r) => (acc.reverse ++ xs, r) := by
  fun_induction readMoreC item hitem s acc with
  | case1 s acc p s₁ h x s₂ hi ih =>
    have e := hsim s₁
    rw [hi, V_ok] at e
    rw [ih, view_of_uncons h, readMore]
    revert e
    rcases itemS (view s₁) with e | ⟨y, r, hr⟩
    · simp
    · simp only [U_ok, Except.ok.injEq, Prod.mk.injEq, okBind, and_imp]
      intro hy hr'
      subst hy hr'
      rcases readMore itemS (view s₂) with e | ⟨xs, r', hr''⟩ <;> simp
  | case2 s acc p s₁ h e he =>
    have e' := hsim s₁
    rw [he, V_error] at e'
    rw [view_of_uncons h, readMore]
    revert e'
    rcases itemS (view s₁) with e | ⟨y, r, hr⟩ <;> simp
  | case3 s acc hn =>
    rw [readMore]
    · simp
    · intro p rest he
      exact not_head hn p rest he

theorem readMoreC_le {item : σ → Except ParseError (α × σ)}
    {hitem : ∀ s a s', item s = .ok (a, s') → (view s').length ≤ (view s).length}
    {s s' : σ} {acc xs : List α} (h : readMoreC item hitem s acc = .ok (xs, s')) :
    (view s').length ≤ (view s).length := by
  fun_induction readMoreC item hitem s acc with
  | case1 s acc p s₁ h₁ x s₂ hi ih =>
    exact Nat.le_trans (ih h) (Nat.le_of_lt (Nat.lt_of_le_of_lt (hitem _ _ _ hi) (length_lt h₁)))
  | case2 => cases h
  | case3 =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ Nat.le_refl _

/-! # Definitions -/

/-- `readDefType`, on a cursor. -/
def readDefTypeC (n : Name) (p : TextPos) (s : σ) : Except ParseError (SDef × σ) :=
  match expectC .colon ": and the value's type" s with
  | .ok ((), s₁) =>
    match readTypeC s₁ with
    | .ok ((ty, tp), s₂) => .ok (⟨n, p, ty, tp⟩, s₂)
    | .error e => .error e
  | .error e => .error e

theorem readDefTypeC_eq (n : Name) (p : TextPos) (s : σ) :
    V (readDefTypeC n p s) = U (readDefType n p (view s)) := by
  unfold readDefTypeC readDefType
  rcases agree (expectC_eq .colon ": and the value's type" s) with
    ⟨e, hx, hy⟩ | ⟨⟨⟩, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [okBind]
    rcases agree (readTypeC_eq s₁) with ⟨e, hx', hy'⟩ | ⟨⟨ty, tp⟩, s₂, r', hr', hx', hy', hv'⟩
    · rw [hx', hy']; rfl
    · rw [hx', hy']
      subst hv'
      rfl

theorem readDefTypeC_le {n : Name} {p : TextPos} {s s' : σ} {d : SDef}
    (h : readDefTypeC n p s = .ok (d, s')) : (view s').length ≤ (view s).length :=
  length_le (readDefTypeC_eq n p s) rfl h

/-- `readDef`, on a cursor. -/
def readDefC (s : σ) : Except ParseError (SDef × σ) :=
  match uncons s with
  | some (⟨.value n, p⟩, s₁) => readDefTypeC n p s₁
  | _ => failC s "a value definition, `%x: type`"

theorem readDefC_eq (s : σ) : V (readDefC s) = U (readDef (view s)) := by
  unfold readDefC
  split
  · rename_i n p s₁ h
    rw [view_of_uncons h, readDef, readDefTypeC_eq]
    rcases readDefType n p (view s₁) with e | ⟨d, r, hr⟩ <;> rfl
  · rename_i hn
    rw [failC_eq, V_fail]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readDef] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readDef] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hn _ _ _)

theorem readDefC_le (s : σ) (d : SDef) (s' : σ) (h : readDefC s = .ok (d, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readDefC_eq s) rfl h

/-- `readDefs`, on a cursor. -/
def readDefsC (s : σ) : Except ParseError (List SDef × σ) :=
  match readDefC s with
  | .ok (d, s₁) =>
    match readMoreC readDefC readDefC_le s₁ [] with
    | .ok (ds, s₂) => .ok (d :: ds, s₂)
    | .error e => .error e
  | .error e => .error e

theorem readDefsC_eq (s : σ) : V (readDefsC s) = U (readDefs (view s)) := by
  unfold readDefsC readDefs
  rcases agree (readDefC_eq s) with ⟨e, hx, hy⟩ | ⟨d, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [okBind]
    rcases agree_map (readMoreC_eq readDefC readDefC_le readDef readDefC_eq s₁ []) with
      ⟨e, hx', hy'⟩ | ⟨ds, s₂, r', hr', hx', hy', hv'⟩
    · rw [hx', hy']; rfl
    · rw [hx', hy']
      subst hv'
      rfl

theorem readDefsC_le {s s' : σ} {ds : List SDef} (h : readDefsC s = .ok (ds, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readDefsC_eq s) rfl h

/-! # Successors and operands -/

/-- `readSuccArgs`, on a cursor: the values read so far are `acc`, last
first. -/
def readSuccArgsC (s : σ) (acc : List Name) : Except ParseError (List Name × σ) :=
  match _h : uncons s with
  | some (⟨.value v, _⟩, s₁) =>
    match _h₁ : uncons s₁ with
    | some (⟨.comma, _⟩, s₂) => readSuccArgsC s₂ (v :: acc)
    | _ =>
      match expectC .rparen ", or ) after the successor's arguments" s₁ with
      | .ok ((), s₂) => .ok ((v :: acc).reverse, s₂)
      | .error e => .error e
  | _ => failC s "a value passed to the successor"
termination_by (view s).length
decreasing_by exact Nat.lt_trans (length_lt _h₁) (length_lt _h)

theorem readSuccArgsC_eq (s : σ) (acc : List Name) :
    V (readSuccArgsC s acc) =
      (U (readSuccArgs (view s))).map fun (vs, r) => (acc.reverse ++ vs, r) := by
  fun_induction readSuccArgsC s acc with
  | case1 s acc v p s₁ h q s₂ h₁ ih =>
    rw [ih, view_of_uncons h, view_of_uncons h₁, readSuccArgs]
    rcases readSuccArgs (view s₂) with e | ⟨vs, r, hr⟩ <;> simp
  | case2 s acc v p s₁ h s₂ hx hn =>
    rw [view_of_uncons h, readSuccArgs]
    · rcases agree (expectC_eq .rparen ", or ) after the successor's arguments" s₁) with
        ⟨e, hx', hy⟩ | ⟨⟨⟩, s₃, r, hr, hx', hy, hv⟩
      · rw [hx] at hx'; cases hx'
      · rw [hx] at hx'
        cases hx'
        rw [hy]
        subst hv
        simp
    · intro q rest he
      exact not_head hn q rest he
  | case3 s acc v p s₁ h e hx hn =>
    rw [view_of_uncons h, readSuccArgs]
    · rcases agree (expectC_eq .rparen ", or ) after the successor's arguments" s₁) with
        ⟨e', hx', hy⟩ | ⟨⟨⟩, s₃, r, hr, hx', hy, hv⟩
      · rw [hx] at hx'
        cases hx'
        rw [hy]
        rfl
      · rw [hx] at hx'; cases hx'
    · intro q rest he
      exact not_head hn q rest he
  | case4 s acc hn =>
    rw [failC_eq, V_fail]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readSuccArgs] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readSuccArgs] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hn _ _ _)

/-- `readSucc`, on a cursor. -/
def readSuccC (s : σ) : Except ParseError (Succ × σ) :=
  match uncons s with
  | some (⟨.label l, _⟩, s₁) =>
    match uncons s₁ with
    | some (⟨.lparen, _⟩, s₂) =>
      match readSuccArgsC s₂ [] with
      | .ok (args, s₃) => .ok (⟨l, args⟩, s₃)
      | .error e => .error e
    | _ => .ok (⟨l, []⟩, s₁)
  | _ => failC s "a successor, such as ^next"

theorem readSuccC_eq (s : σ) : V (readSuccC s) = U (readSucc (view s)) := by
  unfold readSuccC
  split
  · rename_i l p s₁ h
    split
    · rename_i q s₂ h₁
      rw [view_of_uncons h, view_of_uncons h₁, readSucc]
      rcases agree_map (readSuccArgsC_eq s₂ []) with
        ⟨e, hx', hy'⟩ | ⟨args, s₃, r, hr, hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        rfl
    · rename_i hn
      rw [view_of_uncons h, readSucc]
      · rfl
      · intro q rest he
        exact not_head hn q rest he
  · rename_i hn
    rw [failC_eq, V_fail]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readSucc] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readSucc] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hn _ _ _)

theorem readSuccC_le (s : σ) (x : Succ) (s' : σ) (h : readSuccC s = .ok (x, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readSuccC_eq s) rfl h

end FirRef
