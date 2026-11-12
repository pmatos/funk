import FirRef.Lex.Stream

/-!
`fir-ref run` reads each argument, and each choice of `--choices`, as one
token of fir's text (`docs/decisions/fir-ref-command-line.md#fir-ref-run`).
`argAttr` is that reading by the
spec's lexer: the text lexed whole with `Text.lex`, then matched against an
integer, a word or a float literal (ADR-2026-11-11-1438), then `eof`. The spec's lexer builds the list of the
text's characters and measures a comment with `utf8Len`, which takes stack
per character, so a long comment overflows a small stack (#135).

`argAttrP` reads the same over positions: `nextTokP` reads the first token
and, after an integer, a word or a float literal, takes one more step, which must give `eof`
and end the text. It builds no list of the text's characters, takes no
stack per character and lexes at most two tokens. `argAttr_eq_argAttrP`
proves the two equal on every text and registers the equation with
`@[csimp]` (ADR-2026-10-30-1450), so `fir-ref` runs `argAttrP` wherever it
reads an argument.
-/

namespace FirRef

open Fir Fir.Text

/-- The attribute that the text `s` spells as one token: the spec's lexer
reads `s` as an integer, a word or a float literal, then `eof`. -/
def argAttr (s : String) : Option Attr :=
  match Text.lex s with
  | .ok [⟨.int i, _⟩, ⟨.eof, _⟩] => some (Attr.int i)
  | .ok [⟨.word x, _⟩, ⟨.eof, _⟩] => some (Attr.word x)
  | .ok [⟨.float l, _⟩, ⟨.eof, _⟩] => some (Attr.float l)
  | _ => none

/-- `argAttr`, over positions: the first token of `s`, when it is an
integer, a word or a float literal and the lexer's next step gives `eof`
and ends. -/
def argAttrP (s : String) : Option Attr :=
  match nextTokP s.startPos ⟨1, 1⟩ with
  | .ok (⟨.int i, _⟩, some (j, q)) =>
    match nextTokP j q with
    | .ok (⟨.eof, _⟩, none) => some (Attr.int i)
    | _ => none
  | .ok (⟨.word x, _⟩, some (j, q)) =>
    match nextTokP j q with
    | .ok (⟨.eof, _⟩, none) => some (Attr.word x)
    | _ => none
  | .ok (⟨.float l, _⟩, some (j, q)) =>
    match nextTokP j q with
    | .ok (⟨.eof, _⟩, none) => some (Attr.float l)
    | _ => none
  | _ => none

/-- `lex_eq_lexRest` and `lexRest_some` turn the spec's lexer into steps of
`nextTokP`; the first three steps decide the match. -/
@[csimp] theorem argAttr_eq_argAttrP : @argAttr = @argAttrP := by
  funext s
  unfold argAttr argAttrP
  rw [lex_eq_lexRest, lexRest_some]
  rcases nextTokP s.startPos ⟨1, 1⟩ with e | ⟨⟨t, p⟩, _ | ⟨j, q⟩⟩
  · rfl
  · dsimp only
    rw [lexRest_none]
    cases t <;> rfl
  · dsimp only
    rw [lexRest_some]
    cases t
    all_goals
      dsimp only
      rcases nextTokP j q with e | ⟨⟨t₂, p₂⟩, _ | ⟨k, r⟩⟩
      · rfl
      · dsimp only
        rw [lexRest_none]
        cases t₂ <;> rfl
      · dsimp only
        rw [lexRest_some]
        rcases nextTokP k r with e | ⟨t₃, st⟩
        · cases t₂ <;> rfl
        · dsimp only
          rcases lexRest st with e | ts <;> cases t₂ <;> rfl

end FirRef
