import FirRef.Lex.Stream
import FirRef.Read.Cursor

/-!
A `LexCursor` is a lexer's state, as a cursor: `uncons` lexes the next
token from the text when a reader asks for it, so the readers take a text's
tokens without a list of them. Its view is `lexToks`, the tokens from its
state up to the lexer's first error, if any: when the text lexes without
an error from there, they are the tokens that the spec's lexer gives
(`lexToks_of_lexRest`). At a lexer error the cursor ends, so the readers
fail there, and `FirRef.readText` then runs `lexCheck` for the lexer's
error.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

/-- The tokens from a lexer's state on, up to its first error. -/
def lexToks : Option (s.Pos × TextPos) → List Token
  | none => []
  | some (i, p) =>
    match _h : nextTokP i p with
    | .ok (t, st) => t :: lexToks st
    | .error _ => []
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

theorem lexToks_none : lexToks (s := s) none = [] := by
  rw [lexToks]

theorem lexToks_some (i : s.Pos) (p : TextPos) :
    lexToks (some (i, p)) = match nextTokP i p with
      | .ok (t, st) => t :: lexToks st
      | .error _ => [] := by
  rw [lexToks]
  split <;> rename_i heq <;> simp only [heq]

theorem lexToks_of_lexRest (st : Option (s.Pos × TextPos)) :
    ∀ ts, lexRest st = .ok ts → lexToks st = ts := by
  fun_induction lexToks st with
  | case1 =>
    intro ts h
    rw [lexRest_none] at h
    cases h
    rfl
  | case2 i p t st h ih =>
    intro ts h'
    rw [lexRest_some, h] at h'
    dsimp only at h'
    rcases hst : lexRest st with e | ts'
    · rw [hst] at h'
      cases h'
    · rw [hst] at h'
      cases h'
      rw [ih ts' hst]
  | case3 i p e h =>
    intro ts h'
    rw [lexRest_some, h] at h'
    cases h'

/-- A lexer's state in the text `s`, as a source of tokens. -/
structure LexCursor (s : String) where
  /-- Where the next token is looked for, or `none` once `eof` is read. -/
  st : Option (s.Pos × TextPos)

/-- The next token and the state after it. -/
def LexCursor.uncons (c : LexCursor s) : Option (Token × LexCursor s) :=
  match c.st with
  | none => none
  | some (i, p) =>
    match nextTokP i p with
    | .ok (t, st) => some (t, ⟨st⟩)
    | .error _ => none

/-- The view of a lexer's state is the tokens that `uncons` gives, up to
the lexer's first error. -/
instance : Cursor (LexCursor s) where
  uncons := LexCursor.uncons
  view c := lexToks c.st
  view_uncons c := by
    rcases c with ⟨_ | ⟨i, p⟩⟩
    · simp only [LexCursor.uncons, lexToks_none]
    · simp only [LexCursor.uncons, lexToks_some]
      rcases nextTokP i p with e | ⟨t, st⟩ <;> rfl

/-- The lexer's state at the start of a text. -/
def LexCursor.start (text : String) : LexCursor text := ⟨some (text.startPos, ⟨1, 1⟩)⟩

/-- When a text lexes without an error, the cursor at its start holds its
tokens. -/
theorem LexCursor.view_start {text : String} {ts : List Token} (h : lex text = .ok ts) :
    Cursor.view (LexCursor.start text) = ts := by
  rw [lex_eq_lexRest] at h
  exact lexToks_of_lexRest _ ts h

end FirRef
