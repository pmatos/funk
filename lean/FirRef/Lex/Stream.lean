import FirRef.Lex.Rest

/-!
The tokens of a text, one step at a time. A lexer's state is where the next
token is looked for, a position in the text and the text position there, or
`none` once `eof` is read. `lexRest` is the tokens from a state on, and the
spec's `lex text` is `lexRest` from the start (`lex_eq_lexRest`).
`lexCheck` runs the same steps and keeps no token: it fails with the
lexer's error where the text has one, and succeeds where it has none.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

/-- Each step of the lexer that reads a token other than `eof` moves on. -/
theorem nextTokP_lt (i : s.Pos) (p : TextPos) :
    ∀ {t : Token} {j : s.Pos} {q : TextPos}, nextTokP i p = .ok (t, some (j, q)) →
      (chars j).length < (chars i).length := by
  fun_induction nextTokP i p with
  | case1 => intro t j q hn; cases hn
  | case2 i p c i₁ h hc ih | case3 i p i₁ h hc ih =>
    intro t j q hn
    have := ih hn
    have := length_lt_of_peekP h
    omega
  | case4 => intro t j q hn; cases hn
  | case5 i p i₁ i₂ h₁ n j hc h hws hnl ih =>
    intro t j' q hn
    have := ih hn
    have := commentP_le hc
    have := length_lt_of_peekP h₁
    have := length_lt_of_peekP h
    omega
  | case6 i p c i₁ h hws hnl i₂ h₁ hs t j q hx | case8 i p c i₁ h hws hnl t j q hx =>
    intro t' j' q' hn
    cases hn
    have := lexTokenP_le hx
    have := length_lt_of_peekP h
    omega
  | case7 | case9 => intro t j q hn; cases hn

/-- The tokens from a lexer's state on. -/
def lexRest : Option (s.Pos × TextPos) → Except ParseError (List Token)
  | none => .ok []
  | some (i, p) =>
    match _h : nextTokP i p with
    | .ok (t, st) => (lexRest st).map (t :: ·)
    | .error e => .error e
termination_by st => match st with
  | none => 0
  | some (i, _) => (chars i).length + 1
decreasing_by
  cases st with
  | none => simp
  | some v =>
    obtain ⟨j, q⟩ := v
    have := nextTokP_lt i p _h
    simp only
    omega

theorem lexRest_none : lexRest (s := s) none = .ok [] := by
  rw [lexRest]

theorem lexRest_some (i : s.Pos) (p : TextPos) :
    lexRest (some (i, p)) = match nextTokP i p with
      | .ok (t, st) => (lexRest st).map (t :: ·)
      | .error e => .error e := by
  rw [lexRest]
  split <;> rename_i heq <;> simp only [heq]

theorem lexFrom_lexRest (st : Option (s.Pos × TextPos)) :
    ∀ (i : s.Pos) (p : TextPos) (acc : List Token), st = some (i, p) →
      lexFrom (chars i) p acc = (lexRest st).map (acc.reverse ++ ·) := by
  fun_induction lexRest st with
  | case1 => intro i p acc he; cases he
  | case2 i p t st h ih =>
    intro i' p' acc he
    cases he
    rw [lexFrom_eq, h]
    rcases st with _ | ⟨j, q⟩
    · simp [lexRest_none]
    · dsimp only
      rw [ih j q (t :: acc) rfl]
      rcases lexRest (some (j, q)) with e | ts <;> simp
  | case3 i p e h =>
    intro i' p' acc he
    cases he
    rw [lexFrom_eq, h]
    rfl

theorem lex_eq_lexRest (text : String) :
    lex text = lexRest (some (text.startPos, ⟨1, 1⟩)) := by
  rw [lex, ← chars_startPos, lexFrom_lexRest _ _ _ [] rfl]
  cases lexRest (some (text.startPos, ⟨1, 1⟩)) <;> rfl

/-- Runs the lexer from a state and keeps no token: the lexer's error, if
the text from there has one. Every call to itself is a tail call. -/
def lexCheck (i : s.Pos) (p : TextPos) : Except ParseError Unit :=
  match _h : nextTokP i p with
  | .error e => .error e
  | .ok (_, none) => .ok ()
  | .ok (_, some (j, q)) => lexCheck j q
termination_by (chars i).length
decreasing_by exact nextTokP_lt i p _h

theorem lexCheck_eq (i : s.Pos) (p : TextPos) :
    lexCheck i p = (lexRest (some (i, p))).map fun _ => () := by
  fun_induction lexCheck i p with
  | case1 i p e h =>
    rw [lexRest_some, h]
    rfl
  | case2 i p t h =>
    rw [lexRest_some, h]
    dsimp only
    rw [lexRest_none]
    rfl
  | case3 i p t j q h ih =>
    rw [ih, lexRest_some i p, h]
    dsimp only
    rcases lexRest (some (j, q)) with e | ts <;> rfl

end FirRef
