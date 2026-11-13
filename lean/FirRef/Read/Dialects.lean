import FirRef.Read.Lists

/-!
`readDialectsC` reads a dialect set on a cursor, as the spec's
`readDialects` does: at the start of a module, and at the start of a body
of items. `readLayoutC` reads a data layout, as `readLayout` does, after a
module's dialect set.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- `readDialectName`, on a cursor. -/
def readDialectNameC (s : σ) : Except ParseError (Name × σ) :=
  match uncons s with
  | some (⟨.word w, _⟩, s') => .ok (w, s')
  | _ => failC s "the name of a dialect"

theorem readDialectNameC_eq (s : σ) : V (readDialectNameC s) = U (readDialectName (view s)) := by
  unfold readDialectNameC
  split
  · rename_i w p s' h
    rw [view_of_uncons h]
    rfl
  · rename_i hn
    rw [failC_eq, V_fail]
    cases h : uncons s with
    | none => rw [view_of_uncons_none h]; rfl
    | some v =>
      obtain ⟨⟨t, p⟩, s'⟩ := v
      rw [view_of_uncons h]
      cases t <;> first | rfl | exact absurd h (hn _ _ _)

theorem readDialectNameC_le (s : σ) (n : Name) (s' : σ) (h : readDialectNameC s = .ok (n, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readDialectNameC_eq s) rfl h

/-- `readDialects`, on a cursor, with no stack per name. -/
def readDialectsC (s : σ) : Except ParseError (List Name × σ) :=
  match uncons s with
  | some (⟨.word "dialects", _⟩, s₁) =>
    match readDialectNameC s₁ with
    | .ok (n, s₂) =>
      match readMoreC readDialectNameC readDialectNameC_le s₂ [] with
      | .ok (ns, s₃) => .ok (n :: ns, s₃)
      | .error e => .error e
    | .error e => .error e
  | _ => .ok ([], s)

theorem readDialectsC_eq (s : σ) : V (readDialectsC s) = U (readDialects (view s)) := by
  unfold readDialectsC
  split
  · rename_i p s₁ h
    rw [view_of_uncons h, readDialects.eq_1]
    rcases agree (readDialectNameC_eq s₁) with ⟨e, hx, hy⟩ | ⟨n, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [okBind]
      rcases agree_map (readMoreC_eq readDialectNameC readDialectNameC_le readDialectName
        readDialectNameC_eq s₂ []) with ⟨e, hx', hy'⟩ | ⟨ns, s₃, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        rfl
  · rename_i hn
    rw [readDialects.eq_2 _ fun p rest he => not_head hn p rest he]
    rfl

theorem readDialectsC_le {s s' : σ} {ns : List Name} (h : readDialectsC s = .ok (ns, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readDialectsC_eq s) rfl h

theorem readLayoutTypeC_le (s : σ) (a : Attr × TextPos) (s' : σ) (h : readTypeC s = .ok (a, s')) :
    (view s').length ≤ (view s).length :=
  readTypeC_le h

/-- `readLayout`, on a cursor, with no stack per entry. -/
def readLayoutC (s : σ) : Except ParseError (List (Attr × TextPos) × σ) :=
  match uncons s with
  | some (⟨.word "layout", _⟩, s₁) =>
    match readTypeC s₁ with
    | .ok (e, s₂) =>
      match readMoreC readTypeC readLayoutTypeC_le s₂ [] with
      | .ok (es, s₃) => .ok (e :: es, s₃)
      | .error err => .error err
    | .error err => .error err
  | _ => .ok ([], s)

theorem readLayoutC_eq (s : σ) : V (readLayoutC s) = U (readLayout (view s)) := by
  unfold readLayoutC
  split
  · rename_i p s₁ h
    rw [view_of_uncons h, readLayout.eq_1]
    rcases agree (readTypeC_eq s₁) with ⟨e, hx, hy⟩ | ⟨n, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [okBind]
      rcases agree_map (readMoreC_eq readTypeC readLayoutTypeC_le readType
        readTypeC_eq s₂ []) with ⟨e, hx', hy'⟩ | ⟨ns, s₃, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        rfl
  · rename_i hn
    rw [readLayout.eq_2 _ fun p rest he => not_head hn p rest he]
    rfl

end FirRef
