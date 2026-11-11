import FirRef.Lex.Chars

/-!
The parts of a token that the spec's lexer reads with helper functions,
over positions: the digits of a number, an escape in a string, and a
string. Each is proved to give what the spec's function gives on the
characters from its position, with the position after it in place of the
characters after it.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

/-- `lexDigits`, over positions. -/
def lexDigitsP (d : Char) (i : s.Pos) (p : TextPos) : Except ParseError (List Char × s.Pos) :=
  let ds := if d = '0' then ['0'] else d :: takeWhileP Char.isDigit i []
  let j := if d = '0' then i else skipWhileP Char.isDigit i
  match peekP j with
  | some (c, _) => if isNameChar c then errorAt p (runsInto c) else .ok (ds, j)
  | none => .ok (ds, j)

theorem lexDigitsP_eq (d : Char) (i : s.Pos) (p : TextPos) :
    (lexDigitsP d i p).map (fun x => (x.1, chars x.2)) =
      (lexDigits d (chars i) p).map (fun x => (x.1, x.2.1)) := by
  unfold lexDigitsP lexDigits
  have hj : chars (if d = '0' then i else skipWhileP Char.isDigit i) =
      (if d = '0' then (⟨chars i, by simp⟩ : Left (chars i))
        else ⟨(chars i).dropWhile Char.isDigit, length_dropWhile_le _ _⟩).1 := by
    split <;> simp [chars_skipWhileP]
  have hds : (if d = '0' then ['0'] else d :: takeWhileP Char.isDigit i []) =
      (if d = '0' then ['0'] else d :: (chars i).takeWhile Char.isDigit) := by
    split <;> simp [takeWhileP_eq]
  simp only [hds]
  generalize (if d = '0' then i else skipWhileP Char.isDigit i) = j at hj ⊢
  generalize (if d = '0' then (⟨chars i, by simp⟩ : Left (chars i))
    else ⟨(chars i).dropWhile Char.isDigit, length_dropWhile_le _ _⟩) = r at hj ⊢
  generalize (if d = '0' then ['0'] else d :: (chars i).takeWhile Char.isDigit) = ds
  rcases hp : peekP j with _ | ⟨c, j'⟩
  · rw [chars_of_peekP_none hp] at hj
    rw [← hj]
    simp only [okExceptMap, chars_of_peekP_none hp, hj]
  · rw [chars_of_peekP hp] at hj
    rw [← hj]
    simp only
    cases hn : isNameChar c
    · simp only [Bool.false_eq_true, ite_false, okExceptMap]
      rw [chars_of_peekP hp, hj]
    · simp only [ite_true]
      rfl

/-- `lexEscape`, over positions. -/
def lexEscapeP (i : s.Pos) (p : TextPos) : Except ParseError (Char × Nat × s.Pos) :=
  match peekP i with
  | some (c, i₁) =>
    match c with
    | '\\' => .ok ('\\', 1, i₁)
    | '"' => .ok ('"', 1, i₁)
    | 'n' => .ok ('\n', 1, i₁)
    | 't' => .ok ('\t', 1, i₁)
    | 'u' =>
      match peekP i₁ with
      | some ('{', i₂) =>
        match peekP (skipWhileP isHexDigit i₂) with
        | some ('}', j) =>
          let digits := takeWhileP isHexDigit i₂ []
          (unicodeEscape digits p).map (·, 3 + digits.length, j)
        | _ => errorAt p "\\u{ must be followed by lowercase hexadecimal digits and }"
      | _ => errorAt p "a string escape is \\\\, \\\", \\n, \\t or \\u{h}"
    | _ => errorAt p "a string escape is \\\\, \\\", \\n, \\t or \\u{h}"
  | none => errorAt p "a string escape is \\\\, \\\", \\n, \\t or \\u{h}"

theorem lexEscapeP_eq (i : s.Pos) (p : TextPos) :
    (lexEscapeP i p).map (fun x => (x.1, x.2.1, chars x.2.2)) =
      (lexEscape (chars i) p).map (fun x => (x.1, x.2.1, x.2.2.1)) := by
  unfold lexEscapeP
  rcases hp : peekP i with _ | ⟨c, i₁⟩
  · rw [chars_of_peekP_none hp, lexEscape] <;> first | rfl | (intros; simp_all)
  · rw [chars_of_peekP hp]
    simp only
    split
    · rw [lexEscape]; rfl
    · rw [lexEscape]; rfl
    · rw [lexEscape]; rfl
    · rw [lexEscape]; rfl
    · rcases hp₁ : peekP i₁ with _ | ⟨c₁, i₂⟩
      · rw [chars_of_peekP_none hp₁, lexEscape] <;> first | rfl | (intros; simp_all)
      · rw [chars_of_peekP hp₁]
        try simp only
        split
        · rename_i i₂' heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hd := chars_skipWhileP isHexDigit i₂
          rw [lexEscape]
          rcases hq : peekP (skipWhileP isHexDigit i₂) with _ | ⟨c₂, j⟩
          · rw [chars_of_peekP_none hq] at hd
            try simp only
            split
            · rename_i after h
              rw [← hd] at h
              cases h
            · rfl
          · rw [chars_of_peekP hq] at hd
            try simp only
            split
            · rename_i j' heq'
              simp only [Option.some.injEq, Prod.mk.injEq] at heq'
              obtain ⟨rfl, rfl⟩ := heq'
              split
              · rename_i after h
                rw [← hd] at h
                cases h
                simp only [takeWhileP_eq, List.reverse_nil, List.nil_append]
                try dsimp only
                cases unicodeEscape ((chars i₂).takeWhile isHexDigit) p <;> rfl
              · rename_i hn
                exact absurd hd.symm (hn _)
            · rename_i hn
              split
              · rename_i after h
                rw [← hd] at h
                cases h
                exact absurd rfl (hn j)
              · rfl
        · rw [lexEscape] <;> first | rfl | (intros; simp_all)
    · rw [lexEscape] <;> first | rfl | (intros; simp_all)

/-- `lexStringFrom`, over positions: the characters read so far are `acc`,
last first. -/
def lexStringP (i : s.Pos) (p start : TextPos) (acc : List Char) :
    Except ParseError (String × s.Pos × TextPos) :=
  match _h : peekP i with
  | none => errorAt start "the string is not closed"
  | some ('"', i₁) => .ok (String.ofList acc.reverse, i₁, p.advance 1)
  | some ('\\', i₁) =>
    match _he : lexEscapeP i₁ p with
    | .ok (c, width, i₂) => lexStringP i₂ (p.advance (1 + width)) start (c :: acc)
    | .error e => .error e
  | some (c, i₁) =>
    if isEscaped c then errorAt p (codePoint c ++ " must be escaped in a string")
    else lexStringP i₁ (p.advance c.utf8Size) start (c :: acc)
termination_by (chars i).length
decreasing_by
  · have e := lexEscapeP_eq i₁ p
    rw [_he] at e
    have hl := length_lt_of_peekP _h
    revert e
    rcases lexEscape (chars i₁) p with e | ⟨c', w', r, hr⟩
    · simp only [okExceptMap, errorExceptMap, reduceCtorEq, false_implies]
    · simp only [okExceptMap, Except.ok.injEq, Prod.mk.injEq, and_imp]
      intro _ _ hr'
      rw [hr']
      omega
  · exact length_lt_of_peekP _h

end FirRef
