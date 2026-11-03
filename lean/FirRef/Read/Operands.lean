import FirRef.Read.Lists

/-!
The operands and successors of an op, on a cursor. `readMoreOperandsC`
keeps the operands read so far, last first, so a list of any length takes
no stack.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- The successors after the operands `acc`, last first. -/
def succsAfter (s : σ) (acc : List (Name × TextPos)) :
    Except ParseError ((List (Name × TextPos) × List Succ) × σ) :=
  match readMoreC readSuccC readSuccC_le s [] with
  | .ok (ss, s') => .ok ((acc.reverse, ss), s')
  | .error e => .error e

/-- `readMoreOperands`, on a cursor: the operands read so far are `acc`,
last first. -/
def readMoreOperandsC (s : σ) (acc : List (Name × TextPos)) :
    Except ParseError ((List (Name × TextPos) × List Succ) × σ) :=
  match _h : uncons s with
  | some (⟨.comma, _⟩, s₁) =>
    match _h₁ : uncons s₁ with
    | some (⟨.value v, p⟩, s₂) => readMoreOperandsC s₂ ((v, p) :: acc)
    | _ => succsAfter s acc
  | _ => succsAfter s acc
termination_by (view s).length
decreasing_by exact Nat.lt_trans (length_lt _h₁) (length_lt _h)

theorem U_readMoreOperands_succs {ts : List Token}
    (h : ∀ p v q rest, ts ≠ ⟨.comma, p⟩ :: ⟨.value v, q⟩ :: rest) :
    U (readMoreOperands ts) = (do
      let (ss, r) ← U (readMore readSucc ts)
      pure (([], ss), r)) := by
  rw [readMoreOperands]
  · rcases readMore readSucc ts with e | ⟨ss, r, hr⟩ <;> rfl
  · intro a b c d he
    exact h _ _ _ _ he

theorem succsAfter_eq (s : σ) (acc : List (Name × TextPos))
    (h : ∀ p v q rest, view s ≠ ⟨.comma, p⟩ :: ⟨.value v, q⟩ :: rest) :
    V (succsAfter s acc) = (U (readMoreOperands (view s))).map
      fun ((vs, ss), r) => ((acc.reverse ++ vs, ss), r) := by
  rw [U_readMoreOperands_succs h]
  unfold succsAfter
  rcases agree_map (readMoreC_eq readSuccC readSuccC_le readSucc readSuccC_eq s []) with
    ⟨e, hx, hy⟩ | ⟨ss, s', r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp

theorem readMoreOperandsC_eq (s : σ) (acc : List (Name × TextPos)) :
    V (readMoreOperandsC s acc) = (U (readMoreOperands (view s))).map
      fun ((vs, ss), r) => ((acc.reverse ++ vs, ss), r) := by
  fun_induction readMoreOperandsC s acc with
  | case1 s acc p s₁ h v q s₂ h₁ ih =>
    rw [ih, view_of_uncons h, view_of_uncons h₁, readMoreOperands]
    rcases readMoreOperands (view s₂) with e | ⟨⟨vs, ss⟩, r, hr⟩ <;> simp
  | case2 s acc p s₁ h hn =>
    apply succsAfter_eq
    intro p' v q rest he
    rw [view_of_uncons h] at he
    simp only [List.cons.injEq] at he
    exact not_head (hn v) q rest he.2
  | case3 s acc hn =>
    apply succsAfter_eq
    intro p' v q rest he
    exact not_head hn p' _ he

theorem readMoreOperandsC_le {s s' : σ} {acc : List (Name × TextPos)}
    {x : List (Name × TextPos) × List Succ} (h : readMoreOperandsC s acc = .ok (x, s')) :
    (view s').length ≤ (view s).length := by
  rcases agree_map (f := fun (q : List (Name × TextPos) × List Succ) => (acc.reverse ++ q.1, q.2)) (readMoreOperandsC_eq s acc) with
    ⟨e, hx, hy⟩ | ⟨a, s₁, r, hr, hx, hy, hv⟩
  · rw [hx] at h; cases h
  · rw [hx] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2, hv]
    exact hr

/-- `readOperands`, on a cursor. -/
def readOperandsC (s : σ) : Except ParseError ((List (Name × TextPos) × List Succ) × σ) :=
  match uncons s with
  | some (⟨.value v, p⟩, s₁) => readMoreOperandsC s₁ [(v, p)]
  | some (⟨.label _, _⟩, _) =>
    match readSuccC s with
    | .ok (x, s₁) =>
      match readMoreC readSuccC readSuccC_le s₁ [] with
      | .ok (ss, s₂) => .ok (([], x :: ss), s₂)
      | .error e => .error e
    | .error e => .error e
  | _ => .ok (([], []), s)

theorem readOperandsC_eq (s : σ) : V (readOperandsC s) = U (readOperands (view s)) := by
  unfold readOperandsC
  split
  · rename_i v p s₁ h
    rw [view_of_uncons h, readOperands]
    rcases agree_map (f := fun (q : List (Name × TextPos) × List Succ) => ([(v, p)].reverse ++ q.1, q.2)) (readMoreOperandsC_eq s₁ [(v, p)])
      with ⟨e, hx, hy⟩ | ⟨a, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      rfl
  · rename_i l p s₁ h
    rw [view_of_uncons h, readOperands]
    have e₀ := readSuccC_eq s
    rw [view_of_uncons h] at e₀
    rcases agree e₀ with ⟨e, hx, hy⟩ | ⟨x, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [okBind]
      rcases agree_map (readMoreC_eq readSuccC readSuccC_le readSucc readSuccC_eq s₂ []) with
        ⟨e, hx', hy'⟩ | ⟨ss, s₃, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        rfl
  · rename_i hv hl
    simp only [V_ok]
    rcases hu : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hu, readOperands] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hu]
      cases t <;> first
        | exact absurd hu (hv _ _ _)
        | exact absurd hu (hl _ _ _)
        | (rw [readOperands] <;> first | rfl | (intros; simp_all; done))

theorem readOperandsC_le {s s' : σ} {x : List (Name × TextPos) × List Succ}
    (h : readOperandsC s = .ok (x, s')) : (view s').length ≤ (view s).length :=
  length_le (readOperandsC_eq s) rfl h

end FirRef
