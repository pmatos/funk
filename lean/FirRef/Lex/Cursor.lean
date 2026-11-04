import FirRef.Lex.Stream
import FirRef.Read.Cursor

/-!
A `LexCursor` is a lexer's state, as a cursor: the readers take a text's
tokens from it without a list of them. It holds its next token, already
lexed, and the state after it: a position in the text and the line and
column there. `uncons` gives the token it holds and lexes the one after
it, and it is inlined into the readers, so the compiler lexes the token
after it only in the branches where a reader takes the token. A reader
that looks at a token and leaves it, as when a list ends at a token that
is not a comma, lexes nothing, and the reader after it takes the token
from the same cursor: each token is lexed once.

Its view is `lexToks`, the tokens from its state up to the lexer's first
error, if any: when the text lexes without an error from there, they are
the tokens that the spec's lexer gives (`lexToks_of_lexRest`). At a lexer
error the cursor ends, so the readers fail there, and `FirRef.readText`
then runs `lexCheck` for the lexer's error.
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

/-- The next token at a lexer's state and the state after it, or `none`
at the end of the text or at a lexer error. -/
def lookP : Option (s.Pos × TextPos) → Option (Token × Option (s.Pos × TextPos))
  | none => none
  | some (i, p) =>
    match nextTokP i p with
    | .ok r => some r
    | .error _ => none

/-- A lexer's state in the text `s`, with its next token already lexed:
the token and the state after it, or `none` at the end of the text or at a
lexer error. -/
structure LexCursor (s : String) where
  head : Option (Token × Option (s.Pos × TextPos))

/-- The next token, which the cursor holds, and the cursor after it, which
lexes the token after that. It is inlined: where a reader looks at the
token and does not take it, the compiler drops the cursor after it, so the
token after it is lexed only where a reader takes the token. -/
@[inline] def LexCursor.uncons (c : LexCursor s) : Option (Token × LexCursor s) :=
  match c.head with
  | none => none
  | some (t, st) => some (t, ⟨lookP st⟩)

/-- The tokens of a cursor: its next token, then those from the state
after it, up to the lexer's first error. -/
def LexCursor.toks (c : LexCursor s) : List Token :=
  match c.head with
  | none => []
  | some (t, st) => t :: lexToks st

theorem LexCursor.toks_lookP (st : Option (s.Pos × TextPos)) :
    LexCursor.toks (⟨lookP st⟩ : LexCursor s) = lexToks st := by
  rcases st with _ | ⟨i, p⟩
  · rw [lexToks_none]
    rfl
  · rw [lexToks_some]
    unfold LexCursor.toks lookP
    rcases h : nextTokP i p with e | ⟨t, st⟩ <;> simp only [h]

/-- The view of a cursor is the tokens that `uncons` gives, up to the
lexer's first error. -/
instance : Cursor (LexCursor s) where
  uncons := LexCursor.uncons
  view := LexCursor.toks
  view_uncons c := by
    rcases c with ⟨_ | ⟨t, st⟩⟩
    · rfl
    · show t :: lexToks st = t :: LexCursor.toks ⟨lookP st⟩
      rw [LexCursor.toks_lookP]

/-- The lexer's state at the start of a text, with its first token lexed. -/
def LexCursor.start (text : String) : LexCursor text := ⟨lookP (some (text.startPos, ⟨1, 1⟩))⟩

theorem LexCursor.view_start_eq (text : String) :
    Cursor.view (LexCursor.start text) = lexToks (some (text.startPos, ⟨1, 1⟩)) :=
  LexCursor.toks_lookP _

/-- When a text lexes without an error, the cursor at its start holds its
tokens. -/
theorem LexCursor.view_start {text : String} {ts : List Token} (h : lex text = .ok ts) :
    Cursor.view (LexCursor.start text) = ts := by
  rw [view_start_eq]
  rw [lex_eq_lexRest] at h
  exact lexToks_of_lexRest _ ts h

end FirRef
