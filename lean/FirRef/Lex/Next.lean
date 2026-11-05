import FirRef.Lex.Token

/-!
`lexTokenP` reads a token over positions, as the spec's `lexToken` does on
the characters from its position. `nextTokP` skips whitespace and comments
and reads the next token, `eof` at the end of the text, as one step of the
spec's `lexFrom`: `lexFrom_eq` says that `lexFrom` is `nextTokP`, then
`lexFrom` again on the rest.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

/-- The token that a punctuation character is, as `lexToken` reads it. -/
def punctOf (c : Char) : Option Tok :=
  match c with
  | '(' => some .lparen | ')' => some .rparen | '{' => some .lbrace | '}' => some .rbrace
  | ',' => some .comma | ':' => some .colon | '=' => some .eq | _ => none

/-- `lexToken`, over positions: the token that starts with `c`, followed by
the characters from `i`. -/
def lexTokenP (c : Char) (i : s.Pos) (p : TextPos) : Except ParseError (Tok × s.Pos × TextPos) :=
  if !allowedOutsideStrings c then errorAt p (codePoint c ++ " is not allowed outside strings")
  else if let some t := punctOf c then .ok (t, i, p.advance 1)
  else if c = '%' ∨ c = '^' then
    let n := takeWhileP isNameChar i []
    if n.isEmpty then
      errorAt p (if c = '%' then "% must be followed by a value name" else "^ must be followed by a label")
    else
      let name := String.ofList n
      .ok (if c = '%' then .value name else .label name, skipWhileP isNameChar i,
        p.advance (1 + n.length))
  else if c = '@' then lexAtP i p
  else if c = '"' then
    match lexStringP i (p.advance 1) p [] with
    | .ok (str, j, q) => .ok (.str str, j, q)
    | .error e => .error e
  else if c = '-' then
    match peekP i with
    | some ('>', j) => .ok (.arrow, j, p.advance 2)
    | some ('0', _) => errorAt p "-0 is not an integer"
    | some (d, j) =>
      if d.isDigit then lexIntP true d j p
      else errorAt p "- must start a negative integer or ->"
    | none => errorAt p "- must start a negative integer or ->"
  else if c.isDigit then lexIntP false c i p
  else if isWordStart c then
    let w := takeWhileP isNameChar i []
    .ok (.word (String.ofList (c :: w)), skipWhileP isNameChar i, p.advance (1 + w.length))
  else errorAt p ("unexpected character " ++ codePoint c)

-- One proof splits every branch of `lexTokenP` and of `lexToken` and closes
-- some with `simp_all`. It runs out of the default 200,000 heartbeats and
-- passes with 400,000; 1,000,000 leaves room for a change of toolchain.
set_option maxHeartbeats 1000000 in
theorem lexTokenP_eq (c : Char) (i : s.Pos) (p : TextPos) :
    (lexTokenP c i p).map (fun x => (x.1, chars x.2.1, x.2.2)) =
      (lexToken c (chars i) p).map (fun x => (x.1, x.2.1.1, x.2.2)) := by
  unfold lexTokenP lexToken
  split
  · rfl
  -- Punctuation: `punctOf` is the spec's `match`, so both read the same token.
  split
  · rename_i t ht
    split
    all_goals first
      | (cases ht; rfl)
      | (exfalso; unfold punctOf at ht; split at ht <;> simp_all)
  rename_i hn
  symm
  split
  all_goals first | exact (hn _ rfl).elim | skip
  symm
  simp only
  -- The other tokens, one condition at a time; each holds on both sides.
  split
  · simp only [takeWhileP_eq, List.reverse_nil, List.nil_append]
    split
    · rfl
    · simp [chars_skipWhileP]
  split
  · exact lexAtP_eq i p
  split
  · rcases map_agree (lexStringP_nil_eq i (p.advance 1) p) with
      ⟨e, hx, hy⟩ | ⟨⟨str, j, q⟩, ⟨str', ⟨r, hr⟩, q'⟩, hx, hy, hxy⟩
    · rw [hx, hy]
      rfl
    · rw [hx, hy]
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      simp only [okBind, pure, Except.pure, okExceptMap]
  split
  · rcases hp : peekP i with _ | ⟨d, j⟩
    · rw [chars_of_peekP_none hp]
      rfl
    have hc := chars_of_peekP hp
    generalize hcs : chars i = cs
    symm
    split
    · rw [hc] at hcs
      injection hcs with h₁ h₂
      subst h₁ h₂
      rfl
    · rw [hc] at hcs
      injection hcs with h₁ h₂
      subst h₁ h₂
      rfl
    · rw [hc] at hcs
      injection hcs with h₁ h₂
      subst h₁ h₂
      symm
      split
      · exfalso
        simp_all
      · exfalso
        simp_all
      · rename_i heq
        injection heq with heq
        injection heq with h₃ h₄
        subst h₃ h₄
        split
        · rcases map_agree (lexIntP_eq true d j p) with
            ⟨e, hx, hy⟩ | ⟨⟨t, j₂, q⟩, ⟨t', ⟨r, hr⟩, q'⟩, hx, hy, hxy⟩
          · rw [hx, hy]
            rfl
          · rw [hx, hy]
            simp only [Prod.mk.injEq] at hxy
            obtain ⟨rfl, rfl, rfl⟩ := hxy
            simp only [okBind, pure, Except.pure, okExceptMap]
        · rfl
      · rename_i heq
        cases heq
    · rw [hc] at hcs
      cases hcs
  split
  · exact lexIntP_eq false c i p
  split
  · simp [takeWhileP_eq, chars_skipWhileP]
  · rfl

/-- One step of `lexFrom`, over positions: skips whitespace and comments
from `i`, at `p`, and reads the next token, with the position and the
text position after it, or `eof` and `none` at the end of the text. -/
def nextTokP (i : s.Pos) (p : TextPos) :
    Except ParseError (Token × Option (s.Pos × TextPos)) :=
  match _h : peekP i with
  | none => .ok (⟨.eof, p⟩, none)
  | some (c, i₁) =>
    if c = ' ' ∨ c = '\t' then nextTokP i₁ (p.advance 1)
    else if c = '\n' then nextTokP i₁ ⟨p.line + 1, 1⟩
    else
      match _h₁ : peekP i₁ with
      | some ('/', i₂) =>
        if c = '/' then
          match _hc : commentP i₂ 0 with
          | .inl (c', n) => errorAt (p.advance (2 + n)) (codePoint c' ++ " is not allowed outside strings")
          | .inr (n, j) => nextTokP j (p.advance (2 + n))
        else
          match lexTokenP c i₁ p with
          | .ok (t, j, q) => .ok (⟨t, p⟩, some (j, q))
          | .error e => .error e
      | _ =>
        match lexTokenP c i₁ p with
        | .ok (t, j, q) => .ok (⟨t, p⟩, some (j, q))
        | .error e => .error e
termination_by (chars i).length
decreasing_by
  · exact length_lt_of_peekP _h
  · exact length_lt_of_peekP _h
  · have := commentP_le _hc
    have := length_lt_of_peekP _h₁
    have := length_lt_of_peekP _h
    omega

end FirRef
