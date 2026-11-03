import FirRef.Decode
import FirRef.Lex.Cursor
import FirRef.Read.Module

/-!
`fir-ref` parses with `FirRef.parse`, not with the spec's `Fir.parse`
(ADR-2026-10-30-1450). The spec lexes a text into a list of tokens, reads
the list into a tree, and decodes the tree. `FirRef.parse` keeps neither a
list of the text's characters nor a list of its tokens
(ADR-2026-11-03-1810):

* `lexCheck` first runs the lexer over the text's positions and keeps no
  token, so that a lexer error anywhere in the text is reported before any
  error of the readers, as the spec reports it;
* `readModuleC` then reads the tree from a `LexCursor`, which lexes each
  token when a reader asks for it, with readers that take no stack per
  level of nesting;
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
list of the text's characters or tokens. -/
def readText (text : String) : Except ParseError Text.SModule :=
  match lexCheck text.startPos ⟨1, 1⟩ with
  | .ok () => readModuleC (LexCursor.start text)
  | .error e => .error e

theorem readText_eq (text : String) :
    readText text = (do let tokens ← Text.lex text; Text.readModule tokens) := by
  unfold readText
  rw [lexCheck_eq]
  rcases h : Text.lex text with e | ts
  · rw [lex_eq_lexRest] at h
    rw [h]
    rfl
  · have hs := h
    rw [lex_eq_lexRest] at hs
    rw [hs]
    simp only [okExceptMap, okBind]
    rw [readModuleC_eq, LexCursor.view_start h]

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
