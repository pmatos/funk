import FirRef.Read.Operands

/-!
The flat parts of blocks and ops, which the blocks machine reads in one
step each: a block's arguments and colon after its label, and an op's head,
everything before its regions. Each is a reader on a cursor, proved equal to
the same part of the spec's reader. That part is written out as a function
on lists, `blockHeadS`, `opBodyHeadS` or `opWithResultsHeadS`, from the
spec's readers it calls.
-/

namespace FirRef

open Fir Fir.Text Cursor

/-- An op whose regions and location reference are not read yet. -/
structure OpHead where
  results : List SDef
  name : String
  namePos : TextPos
  attrs : List Attr
  operands : List (Name × TextPos)
  succs : List Succ

/-- The op of a head, its regions and its location reference. -/
def OpHead.op (h : OpHead) (regions : List SRegion) (loc : LocRef) : SOp :=
  ⟨h.results, h.name, h.namePos, h.attrs, h.operands, h.succs, regions, loc⟩

/-- What `readBlocks` reads after a block's label: its arguments, if any,
and the colon. -/
def blockHeadS (ts : List Token) : Except ParseError (List SDef × List Token) := do
  let (params, r₁) ← (match ts with
    | ⟨.lparen, _⟩ :: rest => do
      let (ps, a) ← U (readDefs rest)
      let ((), b) ← U (expect .rparen ", or ) after the block's arguments" a)
      pure (ps, b)
    | rest => pure ([], rest))
  let ((), r₂) ← U (expect .colon ": after the block's label" r₁)
  pure (params, r₂)

/-- What `readOpBody` reads before the op's regions. -/
def opBodyHeadS (results : List SDef) (name : String) (namePos : TextPos) (ts : List Token) :
    Except ParseError (OpHead × List Token) := do
  let (attrs, r₁) ← U (readAttrs ts)
  let ((operands, succs), r₂) ← U (readOperands r₁)
  pure (⟨results, name, namePos, attrs.map (·.1), operands, succs⟩, r₂)

/-- What `readOpWithResults` reads before the op's regions. -/
def opWithResultsHeadS (n : Name) (p : TextPos) (ts : List Token) :
    Except ParseError (OpHead × List Token) := do
  let (d, r₁) ← U (readDefType n p ts)
  let (ds, r₂) ← U (readMore readDef r₁)
  match r₂ with
  | ⟨.eq, _⟩ :: ⟨.word w, wp⟩ :: rest => opBodyHeadS (d :: ds) w wp rest
  | ⟨.eq, _⟩ :: rest => fail rest "an op name"
  | _ => fail r₂ "= after the op's results"

variable {σ : Type} [Cursor σ]

/-- `blockHeadS`, on a cursor. -/
def blockHeadC (s : σ) : Except ParseError (List SDef × σ) :=
  match uncons s with
  | some (⟨.lparen, _⟩, s₁) =>
    match readDefsC s₁ with
    | .ok (ps, s₂) =>
      match expectC .rparen ", or ) after the block's arguments" s₂ with
      | .ok ((), s₃) =>
        match expectC .colon ": after the block's label" s₃ with
        | .ok ((), s₄) => .ok (ps, s₄)
        | .error e => .error e
      | .error e => .error e
    | .error e => .error e
  | _ =>
    match expectC .colon ": after the block's label" s with
    | .ok ((), s₁) => .ok ([], s₁)
    | .error e => .error e

theorem blockHeadC_eq (s : σ) : V (blockHeadC s) = blockHeadS (view s) := by
  unfold blockHeadC blockHeadS
  split
  · rename_i p s₁ h
    rw [view_of_uncons h]
    simp only
    rcases agree (readDefsC_eq s₁) with ⟨e, hx, hy⟩ | ⟨ps, s₂, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [U_ok, okBind]
      rcases agree (expectC_eq .rparen ", or ) after the block's arguments" s₂) with
        ⟨e, hx', hy'⟩ | ⟨⟨⟩, s₃, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        simp only [U_ok, okBind, pure_bind]
        rcases agree (expectC_eq .colon ": after the block's label" s₃) with
          ⟨e, hx'', hy''⟩ | ⟨⟨⟩, s₄, r'', hr'', hx'', hy'', hv''⟩
        · rw [hx'', hy'']; rfl
        · rw [hx'', hy'']
          subst hv''
          rfl
  · rename_i hn
    have hs : (match view s with
        | ⟨.lparen, _⟩ :: rest => (do
          let (ps, a) ← U (readDefs rest)
          let ((), b) ← U (expect .rparen ", or ) after the block's arguments" a)
          pure (ps, b) : Except ParseError (List SDef × List Token))
        | rest => pure ([], rest)) = pure ([], view s) := by
      split
      · rename_i p rest he
        exact absurd he (not_head hn p rest)
      · rfl
    rw [hs]
    simp only [pure, Except.pure, okBind]
    rcases agree (expectC_eq .colon ": after the block's label" s) with
      ⟨e, hx, hy⟩ | ⟨⟨⟩, s₁, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      rfl

theorem blockHeadC_le {s s' : σ} {ps : List SDef} (h : blockHeadC s = .ok (ps, s')) :
    (view s').length ≤ (view s).length := by
  unfold blockHeadC at h
  split at h
  · rename_i p s₁ hs
    split at h
    · rename_i ps' s₂ h₂
      split at h
      · rename_i s₃ h₃
        split at h
        · rename_i s₄ h₄
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          have := expectC_lt h₄
          have := expectC_lt h₃
          have := readDefsC_le h₂
          have := length_lt hs
          omega
        · cases h
      · cases h
    · cases h
  · split at h
    · rename_i s₁ h₁
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact Nat.le_of_lt (expectC_lt h₁)
    · cases h

/-- `opBodyHeadS`, on a cursor. -/
def opBodyHeadC (results : List SDef) (name : String) (namePos : TextPos) (s : σ) :
    Except ParseError (OpHead × σ) :=
  match readAttrsC s [] with
  | .ok (attrs, s₁) =>
    match readOperandsC s₁ with
    | .ok ((operands, succs), s₂) =>
      .ok (⟨results, name, namePos, attrs.map (·.1), operands, succs⟩, s₂)
    | .error e => .error e
  | .error e => .error e

theorem opBodyHeadC_eq (results : List SDef) (name : String) (namePos : TextPos) (s : σ) :
    V (opBodyHeadC results name namePos s) = opBodyHeadS results name namePos (view s) := by
  unfold opBodyHeadC opBodyHeadS
  rcases agree_map (f := fun q => ([].reverse ++ q)) (readAttrsC_eq s []) with
    ⟨e, hx, hy⟩ | ⟨attrs, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [U_ok, okBind, List.reverse_nil, List.nil_append]
    rcases agree (readOperandsC_eq s₁) with ⟨e, hx', hy'⟩ | ⟨⟨vs, ss⟩, s₂, r', hr', hx', hy', hv'⟩
    · rw [hx', hy']; rfl
    · rw [hx', hy']
      subst hv'
      rfl

theorem opBodyHeadC_le {results : List SDef} {name : String} {namePos : TextPos} {s s' : σ}
    {hd : OpHead} (h : opBodyHeadC results name namePos s = .ok (hd, s')) :
    (view s').length ≤ (view s).length := by
  unfold opBodyHeadC at h
  split at h
  · rename_i attrs s₁ h₁
    split at h
    · rename_i vs ss s₂ h₂
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact Nat.le_trans (readOperandsC_le h₂) (readAttrsC_le h₁)
    · cases h
  · cases h

/-- `opWithResultsHeadS`, on a cursor. -/
def opWithResultsHeadC (n : Name) (p : TextPos) (s : σ) : Except ParseError (OpHead × σ) :=
  match readDefTypeC n p s with
  | .ok (d, s₁) =>
    match readMoreC readDefC readDefC_le s₁ [] with
    | .ok (ds, s₂) =>
      match uncons s₂ with
      | some (⟨.eq, _⟩, s₃) =>
        match uncons s₃ with
        | some (⟨.word w, wp⟩, s₄) => opBodyHeadC (d :: ds) w wp s₄
        | _ => failC s₃ "an op name"
      | _ => failC s₂ "= after the op's results"
    | .error e => .error e
  | .error e => .error e

theorem opWithResultsHeadC_eq (n : Name) (p : TextPos) (s : σ) :
    V (opWithResultsHeadC n p s) = opWithResultsHeadS n p (view s) := by
  unfold opWithResultsHeadC opWithResultsHeadS
  rcases agree (readDefTypeC_eq n p s) with ⟨e, hx, hy⟩ | ⟨d, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [U_ok, okBind]
    rcases agree_map (f := fun q => ([].reverse ++ q))
      (readMoreC_eq readDefC readDefC_le readDef readDefC_eq s₁ []) with
      ⟨e, hx', hy'⟩ | ⟨ds, s₂, r', hr', hx', hy', hv'⟩
    · rw [hx', hy']; rfl
    · rw [hx', hy']
      subst hv'
      simp only [U_ok, okBind, List.reverse_nil, List.nil_append]
      split
      · rename_i q s₃ h₃
        split
        · rename_i w wp s₄ h₄
          rw [view_of_uncons h₃, view_of_uncons h₄, opBodyHeadC_eq]
        · rename_i hn
          rw [view_of_uncons h₃, failC_eq, V_fail]
          split
          · rename_i w wp rest he
            simp only [List.cons.injEq] at he
            exact absurd he.2 (not_head (hn w) wp rest)
          all_goals simp_all
      · rename_i hn
        rw [failC_eq, V_fail]
        split
        · rename_i he
          exact absurd he (not_head hn _ _)
        · rename_i he
          exact absurd he (not_head hn _ _)
        · rfl

theorem opWithResultsHeadC_le {n : Name} {p : TextPos} {s s' : σ} {hd : OpHead}
    (h : opWithResultsHeadC n p s = .ok (hd, s')) : (view s').length ≤ (view s).length := by
  unfold opWithResultsHeadC at h
  split at h
  · rename_i d s₁ h₁
    split at h
    · rename_i ds s₂ h₂
      split at h
      · rename_i q s₃ h₃
        split at h
        · rename_i w wp s₄ h₄
          have := opBodyHeadC_le h
          have := length_lt h₄
          have := length_lt h₃
          have := readMoreC_le h₂
          have := readDefTypeC_le h₁
          omega
        · rw [failC_eq] at h
          cases hv : view s₃ <;> rw [hv] at h <;> cases h
      · rw [failC_eq] at h
        cases hv : view s₂ <;> rw [hv] at h <;> cases h
    · cases h
  · cases h

end FirRef
