import FirRef.Decode

/-!
`fir-ref` parses with `FirRef.parse`, not with the spec's `Fir.parse`
(ADR-2026-10-30-1450). The two are the same `do` block: lex, read, decode.
The spec compiles `Fir.parse` before any theorem of `FirRef`, and Lean
specializes that compiled body where `fir-ref` calls it, so it would call
the spec's decoder however late the decoder's theorem comes. `FirRef.parse`
is compiled here, after `decodeModule_eq_decodeModule`, so it decodes with
`FirRef.decodeModule`. The theorem `parse_eq_parse` holds by `rfl`, and
`@[csimp]` makes Lean compile every later call of `Fir.parse` as a call of
`FirRef.parse`.

The lexer and the readers are still the spec's. The next stage of #47
replaces them with implementations registered the same way; this module
must import their theorems, so that `FirRef.parse` calls them.

That stage must also fit a text of 10,000,000 ops in memory. Before it
decodes, `fir-ref` holds the whole text as a `List Char`, then as a
`List Token`, then as the read tree, and the first two each take tens of
bytes per input byte (measured in #47). A lexer over `String` positions
that still returns a `List Token` removes only the first. A reader that
pulls each token from the text when it needs it keeps no token list, but
it fuses lexing and reading: it is proved equal to the `do` block below,
not to `lex` alone, and like `Fir.parse` it must report a lexer error
anywhere in the text before any error of the readers.
-/

namespace FirRef

open Fir

/-- `Fir.parse`, compiled after the theorems that replace the spec's
decoder. -/
def parse {d : Dialect} [DialectText d] : Parser d := fun text => do
  let tokens ← Text.lex text
  let tree ← Text.readModule tokens
  Text.decodeModule tree

/-- `FirRef.parse` is `Fir.parse`, so `fir-ref` runs it in its place. -/
@[csimp] theorem parse_eq_parse : @Fir.parse = @parse := rfl

end FirRef
