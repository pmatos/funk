import FirRef.Read.Cursor

/-!
Attributes and types nest to any depth: `h(h(h(x)))`. `attrLoop` reads one
attribute with an explicit stack of frames, one per applied attribute whose
arguments it is reading: the attribute's word and the arguments read so far,
last first. Every call to itself is a tail call, and each consumes a token.
`attrRun` says what a state of the loop means by the spec's readers, and
`attrLoop_eq` proves that the loop computes it, errors included.

`readAttrsC` reads the attributes of an op or an item, as long as one
follows, with an accumulator. It looks at the next token to see whether an
attribute starts there, and `attrFrom` reads the attribute from that token
on, so that a cursor that lexes each token does not lex it again.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- Reads an attribute at `s` when `got` is `none`, or goes on after the
attribute `got`, in the applied attributes that the frames `fs` hold. -/
def attrLoop (s : σ) (got : Option Attr) (fs : List (String × List Attr)) :
    Except ParseError (Attr × σ) :=
  match got with
  | none =>
    match _h : uncons s with
    | some (⟨.word w, _⟩, s₁) =>
      match _h₁ : uncons s₁ with
      | some (⟨.lparen, _⟩, s₂) =>
        match _h₂ : uncons s₂ with
        | some (⟨.rparen, _⟩, s₃) => attrLoop s₃ (some (.app w [])) fs
        | _ => attrLoop s₂ none ((w, []) :: fs)
      | _ => attrLoop s₁ (some (.word w)) fs
    | some (⟨.int i, _⟩, s₁) => attrLoop s₁ (some (.int i)) fs
    | some (⟨.str x, _⟩, s₁) => attrLoop s₁ (some (.str x)) fs
    | some (⟨.sym x, _⟩, s₁) => attrLoop s₁ (some (.sym x)) fs
    | _ => failC s "an attribute"
  | some a =>
    match fs with
    | [] => .ok (a, s)
    | (w, done) :: fs =>
      match _h : uncons s with
      | some (⟨.comma, _⟩, s₁) => attrLoop s₁ none ((w, a :: done) :: fs)
      | some (⟨.rparen, _⟩, s₁) => attrLoop s₁ (some (.app w (a :: done).reverse)) fs
      | _ => failC s ", or ) in the attribute's arguments"
termination_by (view s).length
decreasing_by
  all_goals first
    | exact length_lt _h
    | exact Nat.lt_trans (length_lt _h₁) (length_lt _h)
    | exact Nat.lt_trans (length_lt _h₂) (Nat.lt_trans (length_lt _h₁) (length_lt _h))

/-- The arguments of the applied attributes that the frames hold, read on
by the spec's readers after the argument `a`. -/
def attrFinish (a : Attr) (ts : List Token) :
    List (String × List Attr) → Except ParseError (Attr × List Token)
  | [] => .ok (a, ts)
  | (w, done) :: fs => do
    let (as, r) ← U (readMoreAttrArgs ts)
    attrFinish (.app w (done.reverse ++ a :: as)) r fs

/-- What `attrLoop` computes, by the spec's readers. -/
def attrRun (ts : List Token) : Option Attr → List (String × List Attr) →
    Except ParseError (Attr × List Token)
  | none, fs => do
    let (a, r) ← U (readAttr ts)
    attrFinish a r fs
  | some a, fs => attrFinish a ts fs

theorem U_readAttrArgs {ts : List Token} (h : ∀ p rest, ts ≠ ⟨.rparen, p⟩ :: rest) :
    U (readAttrArgs ts) = (do
      let (a, r) ← U (readAttr ts)
      let (as, r') ← U (readMoreAttrArgs r)
      pure (a :: as, r')) := by
  rw [readAttrArgs]
  · rcases readAttr ts with e | ⟨a, r, hr⟩
    · rfl
    · simp only [okBind, U_ok]
      rcases readMoreAttrArgs r with e | ⟨as, r', hr'⟩ <;> rfl
  · exact h

theorem U_readAttr_app (w : String) (p q : TextPos) (rest : List Token) :
    U (readAttr (⟨.word w, p⟩ :: ⟨.lparen, q⟩ :: rest)) =
      (do let (args, r) ← U (readAttrArgs rest); pure (.app w args, r)) := by
  rw [readAttr]
  rcases readAttrArgs rest with e | ⟨a, r, hr⟩ <;> rfl

theorem U_readAttr_word (w : String) (p : TextPos) {rest : List Token}
    (h : ∀ q rest', rest ≠ ⟨.lparen, q⟩ :: rest') :
    U (readAttr (⟨.word w, p⟩ :: rest)) = .ok (.word w, rest) := by
  rw [readAttr]
  · rfl
  · intro q rest' he
    exact h q rest' he

theorem U_readMoreAttrArgs_comma (p : TextPos) (rest : List Token) :
    U (readMoreAttrArgs (⟨.comma, p⟩ :: rest)) = (do
      let (a, r) ← U (readAttr rest)
      let (as, r') ← U (readMoreAttrArgs r)
      pure (a :: as, r')) := by
  rw [readMoreAttrArgs]
  rcases readAttr rest with e | ⟨a, r, hr⟩
  · rfl
  · simp only [okBind, U_ok]
    rcases readMoreAttrArgs r with e | ⟨as, r', hr'⟩ <;> rfl

/-- The loop reads what the spec's readers read, and fails where they
fail. -/
theorem attrLoop_eq (s : σ) (got : Option Attr) (fs : List (String × List Attr)) :
    V (attrLoop s got fs) = attrRun (view s) got fs := by
  fun_induction attrLoop s got fs with
  | case1 s fs w p s₁ h q s₂ h₁ r s₃ h₂ ih =>
    rw [ih, view_of_uncons h, view_of_uncons h₁, view_of_uncons h₂]
    simp only [attrRun]
    rw [readAttr, readAttrArgs]
    rfl
  | case2 s fs w p s₁ h q s₂ h₁ hn ih =>
    rw [ih, view_of_uncons h, view_of_uncons h₁]
    simp only [attrRun]
    rw [U_readAttr_app, U_readAttrArgs (not_head hn)]
    rcases U (readAttr (view s₂)) with e | ⟨a, r⟩
    · rfl
    · simp only [okBind, attrFinish]
      rcases U (readMoreAttrArgs r) with e | ⟨as, r'⟩
      · rfl
      · simp
  | case3 s fs w p s₁ h hn ih =>
    rw [ih, view_of_uncons h]
    simp only [attrRun]
    rw [U_readAttr_word w p (not_head hn)]
    rfl
  | case4 s fs i p s₁ h ih | case5 s fs i p s₁ h ih | case6 s fs i p s₁ h ih =>
    rw [ih, view_of_uncons h]
    simp only [attrRun]
    rw [readAttr]
    rfl
  | case7 s fs hw hi hs hy =>
    rw [failC_eq]
    simp only [attrRun]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readAttr] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readAttr] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hw _ _ _)
        | exact absurd hv (hi _ _ _)
        | exact absurd hv (hs _ _ _)
        | exact absurd hv (hy _ _ _)
  | case8 s a => rfl
  | case9 s a w done fs p s₁ h ih =>
    rw [ih, view_of_uncons h]
    simp only [attrRun, attrFinish]
    rw [U_readMoreAttrArgs_comma]
    rcases U (readAttr (view s₁)) with e | ⟨b, r⟩
    · rfl
    · simp only [okBind]
      rcases U (readMoreAttrArgs r) with e | ⟨bs, r'⟩
      · rfl
      · simp
  | case10 s a w done fs p s₁ h ih =>
    rw [ih, view_of_uncons h]
    simp only [attrRun, attrFinish]
    rw [readMoreAttrArgs]
    simp
  | case11 s a w done fs hc hr =>
    rw [failC_eq]
    simp only [attrRun, attrFinish]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readMoreAttrArgs] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readMoreAttrArgs] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hc _ _)
        | exact absurd hv (hr _ _)

/-- `readAttr`, on a cursor, with no stack per level. -/
def readAttrC (s : σ) : Except ParseError (Attr × σ) := attrLoop s none []

theorem readAttrC_eq (s : σ) : V (readAttrC s) = U (readAttr (view s)) := by
  rw [readAttrC, attrLoop_eq]
  simp only [attrRun]
  rcases U (readAttr (view s)) with e | ⟨a, r⟩ <;> rfl

theorem readAttrC_lt {s s' : σ} {a : Attr} (h : readAttrC s = .ok (a, s')) :
    (view s').length < (view s).length :=
  length_lt' (readAttrC_eq s) rfl h

/-- `readAttrC`, after the word `w` of an applied attribute and its `(`,
with `s₂` the cursor after them. -/
def attrApp (w : String) (s₂ : σ) : Except ParseError (Attr × σ) :=
  match uncons s₂ with
  | some (⟨.rparen, _⟩, s₃) => attrLoop s₃ (some (.app w [])) []
  | _ => attrLoop s₂ none [(w, [])]

/-- `readAttrC s`, when `uncons s` gave the token `t` and the cursor `s₁`:
a reader that looked at `t` reads the attribute without lexing `t` again. -/
def attrFrom (s : σ) (t : Token) (s₁ : σ) : Except ParseError (Attr × σ) :=
  match t with
  | ⟨.word w, _⟩ =>
    match uncons s₁ with
    | some (⟨.lparen, _⟩, s₂) => attrApp w s₂
    | _ => attrLoop s₁ (some (.word w)) []
  | ⟨.int i, _⟩ => attrLoop s₁ (some (.int i)) []
  | ⟨.str x, _⟩ => attrLoop s₁ (some (.str x)) []
  | ⟨.sym x, _⟩ => attrLoop s₁ (some (.sym x)) []
  | _ => failC s "an attribute"

theorem attrFrom_eq {s s₁ : σ} {t : Token} (h : uncons s = some (t, s₁)) :
    attrFrom s t s₁ = readAttrC s := by
  rw [readAttrC, attrLoop]
  split
  · rename_i w p s₁' heq
    rw [h] at heq
    cases heq
    simp only [attrFrom, attrApp]
    rcases h1 : uncons s₁ with _ | ⟨⟨tk, q⟩, s₂⟩
    · rfl
    · cases tk <;> try rfl
      dsimp only
      rcases h2 : uncons s₂ with _ | ⟨⟨tk', q'⟩, s₃⟩
      · rfl
      · cases tk' <;> rfl
  all_goals first
    | (rename_i heq; rw [h] at heq; cases heq; rfl)
    | skip
  rename_i hw hi hx hy
  rcases t with ⟨tk, p⟩
  cases tk <;> first
    | rfl
    | exact absurd h (hw _ _ _)
    | exact absurd h (hi _ _ _)
    | exact absurd h (hx _ _ _)
    | exact absurd h (hy _ _ _)

theorem attrApp_eq {s s₁ s₂ : σ} {w : String} {p q : TextPos}
    (h : uncons s = some (⟨.word w, p⟩, s₁)) (h₁ : uncons s₁ = some (⟨.lparen, q⟩, s₂)) :
    attrApp w s₂ = readAttrC s := by
  rw [← attrFrom_eq h]
  simp only [attrFrom, h₁]

/-- `readType`, on a cursor, with no stack per level. -/
def readTypeC (s : σ) : Except ParseError ((Attr × TextPos) × σ) :=
  match uncons s with
  | some (⟨.word w, p⟩, s₁) =>
    match uncons s₁ with
    | some (⟨.lparen, _⟩, s₂) =>
      match attrApp w s₂ with
      | .ok (a, s') => .ok ((a, p), s')
      | .error e => .error e
    | _ => .ok ((.word w, p), s₁)
  | _ => failC s "a type"

theorem readTypeC_eq (s : σ) : V (readTypeC s) = U (readType (view s)) := by
  unfold readTypeC
  split
  · rename_i w p s₁ h
    split
    · rename_i q s₂ h₁
      have e := readAttrC_eq s
      rw [← attrApp_eq h h₁, view_of_uncons h, view_of_uncons h₁, U_readAttr_app] at e
      rw [view_of_uncons h, view_of_uncons h₁, readType]
      revert e
      rcases attrApp w s₂ with e | ⟨a, s'⟩ <;> rcases readAttrArgs (view s₂) with e' | ⟨args, r, hr'⟩ <;>
        simp
    · rename_i hn
      rw [view_of_uncons h, readType]
      · rfl
      · intro q rest he
        exact not_head hn q rest he
  · rename_i hn
    rw [failC_eq, V_fail]
    rcases hv : uncons s with _ | ⟨⟨t, p⟩, s₁⟩
    · rw [view_of_uncons_none hv, readType] <;> first | rfl | (intros; simp_all)
    · rw [view_of_uncons hv]
      cases t <;> first
        | (rw [readType] <;> first | rfl | (intros; simp_all))
        | exact absurd hv (hn _ _ _)

theorem readTypeC_le {s s' : σ} {a : Attr × TextPos} (h : readTypeC s = .ok (a, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readTypeC_eq s) rfl h

/-- `readAttrs`, on a cursor: the attributes read so far are `acc`, last
first. Its only call to itself is a tail call. -/
def readAttrsC (s : σ) (acc : List (Attr × TextPos)) :
    Except ParseError (List (Attr × TextPos) × σ) :=
  match _hu : uncons s with
  | some (t, s₁) =>
    if t.tok.startsAttr then
      match _h : attrFrom s t s₁ with
      | .ok (a, s') => readAttrsC s' ((a, t.pos) :: acc)
      | .error e => .error e
    else .ok (acc.reverse, s)
  | none => .ok (acc.reverse, s)
termination_by (view s).length
decreasing_by exact readAttrC_lt ((attrFrom_eq _hu).symm.trans _h)

theorem readAttrsC_eq (s : σ) (acc : List (Attr × TextPos)) :
    V (readAttrsC s acc) = (U (readAttrs (view s))).map fun (xs, r) => (acc.reverse ++ xs, r) := by
  fun_induction readAttrsC s acc with
  | case1 s acc t s₁ h hs a s' ha ih =>
    rw [attrFrom_eq h] at ha
    have e := readAttrC_eq s
    rw [ha, view_of_uncons h] at e
    rw [ih, view_of_uncons h, readAttrs]
    simp only [hs, ite_true]
    revert e
    rcases readAttr (t :: view s₁) with e | ⟨b, r, hr⟩
    · simp
    · simp only [V_ok, U_ok, Except.ok.injEq, Prod.mk.injEq, okBind, and_imp]
      intro hb hr'
      subst hb hr'
      rcases readAttrs (view s') with e | ⟨xs, r', hr''⟩ <;> simp
  | case2 s acc t s₁ h hs e he =>
    rw [attrFrom_eq h] at he
    have e' := readAttrC_eq s
    rw [he, view_of_uncons h] at e'
    rw [view_of_uncons h, readAttrs]
    simp only [hs, ite_true]
    revert e'
    rcases readAttr (t :: view s₁) with e | ⟨b, r, hr⟩ <;> simp [Except.map]
  | case3 s acc t s₁ h hs =>
    rw [view_of_uncons h, readAttrs]
    simp [hs, view_of_uncons h]
  | case4 s acc h =>
    rw [view_of_uncons_none h, readAttrs]
    simp [view_of_uncons_none h]

theorem readAttrsC_le {s s' : σ} {acc a : List (Attr × TextPos)}
    (h : readAttrsC s acc = .ok (a, s')) : (view s').length ≤ (view s).length := by
  have e := readAttrsC_eq s acc
  rw [h, V_ok] at e
  revert e
  rcases hr : readAttrs (view s) with e | ⟨xs, r, hr'⟩
  · simp [Except.map]
  · simp only [U_ok, Except.map, Except.ok.injEq, Prod.mk.injEq, and_imp]
    intro _ he
    exact he ▸ hr'

end FirRef
