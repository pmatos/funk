import FirRef.Read.Lists

/-!
The location table's readers, on a cursor. The table has a fixed syntax;
only its entries and the references of a fused location form lists, which
`readLocEntriesC` and `readMoreC` read with an accumulator.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- `readNat`, on a cursor. -/
def readNatC (what : String) (s : σ) : Except ParseError (Nat × σ) :=
  match uncons s with
  | some (⟨.int (.ofNat n), p⟩, s₁) =>
    if n < Location.limit then .ok (n, s₁)
    else .error ⟨p, s!"{what} {n} is out of range: it must be below 2^32"⟩
  | _ => failC s what

theorem readNatC_eq (what : String) (s : σ) : V (readNatC what s) = U (readNat what (view s)) := by
  unfold readNatC
  split
  · rename_i n p s₁ h
    rw [view_of_uncons h, readNat]
    split <;> rfl
  · rename_i hn
    rw [failC_eq, V_fail]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readNat] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t with
      | int i =>
        cases i with
        | ofNat n => exact absurd hv (hn n p s₁)
        | negSucc n => rw [readNat] <;> first | rfl | (intros; simp_all)
      | _ => rw [readNat] <;> first | rfl | (intros; simp_all)

/-- `readRange`, on a cursor. -/
def readRangeC (file : String) (s : σ) : Except ParseError (Location × σ) := do
  let ((), s₁) ← expectC .colon ": after the file" s
  let (l₁, s₂) ← readNatC "a line" s₁
  let ((), s₃) ← expectC .colon ":" s₂
  let (c₁, s₄) ← readNatC "a column" s₃
  let ((), s₅) ← keywordC "to" s₄
  let (l₂, s₆) ← readNatC "a line" s₅
  let ((), s₇) ← expectC .colon ":" s₆
  let (c₂, s₈) ← readNatC "a column" s₇
  pure (.range file l₁ c₁ l₂ c₂, s₈)

theorem readRangeC_eq (file : String) (s : σ) :
    V (readRangeC file s) = U (readRange file (view s)) := by
  unfold readRangeC readRange
  agree_step (expectC_eq .colon ": after the file" s) with ⟨⟩ s₁
  agree_step (readNatC_eq "a line" s₁) with l₁ s₂
  agree_step (expectC_eq .colon ":" s₂) with ⟨⟩ s₃
  agree_step (readNatC_eq "a column" s₃) with c₁ s₄
  agree_step (keywordC_eq "to" s₄) with ⟨⟩ s₅
  agree_step (readNatC_eq "a line" s₅) with l₂ s₆
  agree_step (expectC_eq .colon ":" s₆) with ⟨⟩ s₇
  agree_step (readNatC_eq "a column" s₇) with c₂ s₈
  rfl

theorem readLocRefC_le (s : σ) (r : LocRef) (s' : σ) (h : readLocRefC s = .ok (r, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readLocRefC_eq s) rfl h

/-- What `readLocArgs` reads before the `)`, on a cursor. -/
def locArgsC (kind : String) (s : σ) : Except ParseError (Location × σ) :=
  match kind with
  | "name" =>
    match uncons s with
    | some (⟨.str n, _⟩, s₁) => .ok (.name n, s₁)
    | _ => failC s "the name, as a string"
  | "callsite" => do
    let (callee, s₁) ← readLocRefC s
    let ((), s₂) ← keywordC "at" s₁
    let (caller, s₃) ← readLocRefC s₂
    pure (.callsite callee caller, s₃)
  | "fused" =>
    match uncons s with
    | some (⟨.rparen, _⟩, _) => .ok (.fused [], s)
    | _ => do
      let (r, s₁) ← readLocRefC s
      let (rs, s₂) ← readMoreC readLocRefC readLocRefC_le s₁ []
      pure (.fused (r :: rs), s₂)
  | _ => do
    let (src, s₁) ← readLocRefC s
    pure (.derived src, s₁)

/-- `readLocArgs`, on a cursor. -/
def readLocArgsC (kind : String) (s : σ) : Except ParseError (Location × σ) := do
  let (loc, s₁) ← locArgsC kind s
  let ((), s₂) ← expectC .rparen ")" s₁
  pure (loc, s₂)

theorem readLocArgsC_eq (kind : String) (s : σ) :
    V (readLocArgsC kind s) = U (readLocArgs kind (view s)) := by
  unfold readLocArgsC readLocArgs
  have hrest : ∀ (x : Except ParseError (Location × σ))
      (y : Except ParseError (Location × After (view s))), V x = U y →
      V (do
        let (loc, s₁) ← x
        let ((), s₂) ← expectC .rparen ")" s₁
        pure (loc, s₂)) =
      U (do
        let (loc, a) ← y
        let ((), b) ← expect .rparen ")" a.1
        pure (loc, a.then b)) := by
    intro x y hxy
    rcases agree hxy with ⟨e, hx, hy⟩ | ⟨loc, s₁, r, hr, hx, hy, hv⟩
    · rw [hx, hy]; rfl
    · rw [hx, hy]
      subst hv
      simp only [okBind]
      rcases agree (expectC_eq .rparen ")" s₁) with
        ⟨e, hx', hy'⟩ | ⟨⟨⟩, s₂, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        rfl
  apply hrest
  clear hrest
  split
  · simp only [locArgsC]
    split
    · rename_i n q s₁ h
      rw [view_of_uncons h]
      rfl
    · rename_i hn
      rw [failC_eq, V_fail]
      cases h : uncons s with
      | none => rw [view_of_uncons_none h]; rfl
      | some v =>
        obtain ⟨⟨t, q⟩, s'⟩ := v
        rw [view_of_uncons h]
        cases t <;> first | rfl | exact absurd h (hn _ _ _)
  · simp only [locArgsC]
    agree_step (readLocRefC_eq s) with callee s₁
    agree_step (keywordC_eq "at" s₁) with ⟨⟩ s₂
    agree_step (readLocRefC_eq s₂) with caller s₃
    rfl
  · simp only [locArgsC]
    split
    · rename_i q s₁ h
      rw [V_ok, view_of_uncons h]
      rfl
    · rename_i hn
      generalize hts : view s = ts
      split
      · rename_i q tl
        exact absurd hts (not_head hn q tl)
      · subst hts
        agree_step (readLocRefC_eq s) with r s₁
        rcases agree_map (f := fun q => ([].reverse ++ q))
          (readMoreC_eq readLocRefC readLocRefC_le readLocRef readLocRefC_eq s₁ []) with
          ⟨e, hx, hy⟩ | ⟨rs, s₂, r', hr', hx, hy, hv⟩
        · rw [hx, hy]; rfl
        · rw [hx, hy]
          subst hv
          rfl
  · simp only [locArgsC]
    agree_step (readLocRefC_eq s) with src s₁
    rfl

/-- `readLocation`, on a cursor. -/
def readLocationC (s : σ) : Except ParseError (Location × σ) :=
  match uncons s with
  | some (⟨.str file, _⟩, s₁) => readRangeC file s₁
  | some (⟨.word "unknown", _⟩, s₁) => .ok (.unknown, s₁)
  | some (⟨.word kind, p⟩, s₁) =>
    if kind ∈ ["name", "callsite", "fused", "derived"] then do
      let ((), s₂) ← expectC .lparen "(" s₁
      readLocArgsC kind s₂
    else .error ⟨p, kind ++ " is not a kind of location"⟩
  | _ => failC s "a location"

theorem readLocationC_eq (s : σ) : V (readLocationC s) = U (readLocation (view s)) := by
  unfold readLocationC
  split
  · rename_i file p s₁ h
    rw [view_of_uncons h, readLocation, readRangeC_eq]
    rcases readRange file (view s₁) with e | ⟨l, r, hr⟩ <;> rfl
  · rename_i p s₁ h
    rw [view_of_uncons h, readLocation]
    rfl
  · rename_i kind p s₁ hk h
    rw [view_of_uncons h, readLocation]
    · split
      · agree_step (expectC_eq .lparen "(" s₁) with ⟨⟩ s₂
        rw [readLocArgsC_eq]
        rcases readLocArgs kind (view s₂) with e | ⟨l, r, hr⟩ <;> rfl
      · rfl
    · first | exact hk | (intros; simp_all)
  · rename_i hs hu hw
    rw [failC_eq, V_fail]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readLocation] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readLocation] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hs _ _ _)
        | exact absurd hv (hw _ _ _)

theorem readLocationC_le {s s' : σ} {l : Location} (h : readLocationC s = .ok (l, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readLocationC_eq s) rfl h

end FirRef
