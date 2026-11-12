import FirRef.Decode
import FirRef.Lex.Eof
import FirRef.Read.Eof

/-!
`fir-ref` parses with `FirRef.parse`, not with the spec's `Fir.parse`
(ADR-2026-10-30-1450). The spec lexes a text into a list of tokens, reads the
list into a tree, and decodes the tree. `FirRef.parse` keeps neither a list of
the text's characters nor a list of its tokens
(`docs/decisions/fir-ref-fast-paths.md#lexing-and-reading`):

* `readModuleC` reads the tree from a `LexCursor`, with readers that take
  no stack per level of nesting. The cursor holds its next token, already
  lexed, and lexes the one after it only where a reader takes the token,
  so each token is lexed once. The cursor ends at a lexer error, so the
  readers fail there;
* only when the readers fail does `lexCheck` run the lexer over the whole
  text, keeping no token, so that a lexer error anywhere in the text is
  reported before the readers' error, as the spec reports it. When the
  readers accept, they took `eof`, which the lexer reads only at the end
  of a text that it reads without an error (`lexRest_of_eof_mem`);
* `Text.decodeModule` decodes the tree, and `@[csimp]` compiles it as
  `FirRef.decodeModule`.

`parse_eq_parse` proves `FirRef.parse` equal to `Fir.parse`, and
`@[csimp]` makes Lean compile every later call of `Fir.parse` as a call of
`FirRef.parse`. `FirRef.parse` is compiled here, after the theorems of the
lexer, the readers and the decoder, so it calls their code, not the
spec's.
-/

namespace FirRef

open Fir

/-- The tree of a text, as the spec's lexer and readers give it, without a
list of the text's characters or tokens. Each token is lexed once when the
readers accept the text, and the text is lexed whole a second time only
when they fail. -/
def readText (text : String) : Except ParseError Text.SModule :=
  match readModuleC (LexCursor.start text) with
  | .ok m => .ok m
  | .error e =>
    match lexCheck text.startPos ⟨1, 1⟩ with
    | .ok () => .error e
    | .error le => .error le

theorem readText_eq (text : String) :
    readText text = (do let tokens ← Text.lex text; Text.readModule tokens) := by
  unfold readText
  rw [readModuleC_eq, lexCheck_eq]
  rcases hl : lexRest (some (text.startPos, (⟨1, 1⟩ : TextPos))) with le | ts
  · have h : Text.lex text = .error le := by rw [lex_eq_lexRest, hl]
    rw [h]
    rcases hr : Text.readModule (Cursor.view (LexCursor.start text)) with e | m
    · rfl
    · -- The readers accepted, so they took `eof`, and the text lexes.
      exfalso
      obtain ⟨t, ht, he⟩ := readModule_ok_eof hr
      rw [LexCursor.view_start_eq] at ht
      obtain ⟨ts, hts⟩ := lexRest_of_eof_mem (some (text.startPos, ⟨1, 1⟩)) t ht he
      rw [hl] at hts
      cases hts
  · have h : Text.lex text = .ok ts := by rw [lex_eq_lexRest, hl]
    rw [h, LexCursor.view_start h]
    simp only [okBind]
    rcases Text.readModule ts with e | m <;> rfl

/-- `Fir.parse`, without a list of characters or tokens, and with the
readers and the decoder that take no stack per level of nesting. -/
def parse {d : Dialect} [DialectText d] : Parser d := fun text => do
  let tree ← readText text
  Text.decodeModule tree

/-- `FirRef.parse` is `Fir.parse`, so `fir-ref` runs it in its place. -/
@[csimp] theorem parse_eq_parse : @Fir.parse = @parse := by
  funext d _ text
  simp only [Fir.parse, parse, readText_eq, bind_assoc]

end FirRef
