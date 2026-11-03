import Fir.Text.DecodeModule
import Fir.Text.ReadModule
import Fir.Core.TextLaws

/-!
# Parsing a printed module

The parser reads a text in three steps, and the proof of the round trip
has one for each. The lexer reads the printed text of a module as the
module's tokens, `Module.tokens` (`lex_print`). The grammar reads those
tokens, at any positions, as the module's tree, `Module.tree`, up to
positions (`readModule_tokens`). Decoding gives the module back from any
tree that erases to its tree (`Module.WellFormed.decodeModule_eq`). Each
step needs only part of what `Module.WellFormed` says, and a well-formed
module has all of it. So `parse(print(m)) == m` for every well-formed
module `m` of every dialect whose text is lawful: `printThenParse`, the
spec's `PrintThenParse` for the parser `Fir.parse`.

The second round trip, `print(parse(t)) == t` for every text `t` printed
from a well-formed module, follows: `parseThenPrint`. So does injectivity:
two well-formed modules that print the same text are the same module
(`Module.WellFormed.print_injective`). Every valid module is well formed
(`validIsWellFormed`), so both hold for valid modules too. With
`Core.lawfulDialectText`, all of it holds for the core dialect.

# What a new dialect or a new core op needs

The proof uses nothing of a dialect but the seven laws of
`LawfulDialectText`, so it covers every lawful dialect at once:

* a new dialect gets the round trip by proving its own `LawfulDialectText`;
* a change to the core op set, such as a new op or a new flag, extends the
  proof of `LawfulDialectText CoreDialect`, `Core.lawfulDialectText`, case
  by case.

Neither reworks the proof of `PrintThenParse`. A new kind of item (H4, H5)
is a change to the parser itself, since `decodeItem` must learn to decode
it, and so it extends the decoding step of this proof.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectSignature d] [DialectValidation d] [DialectText d]
  [LawfulDialectText d]

/-- `parse(print(m)) == m` for every well-formed module `m` of a dialect
whose text is lawful. -/
theorem printThenParse : PrintThenParse (d := d) Fir.parse := by
  intro m hm
  obtain ⟨ts, s, h₁, h₂, h₃⟩ := hm.read_print
  simp only [Fir.parse, h₁, ok_bind, h₂, hm.decodeModule_eq h₃]

/-- `print(parse(t)) == t` for every text `t` printed from a well-formed
module of a dialect whose text is lawful. -/
theorem parseThenPrint : ParseThenPrint (d := d) Fir.parse :=
  parseThenPrint_of_printThenParse printThenParse

/-- A well-formed module reads back from its printed text. -/
theorem Module.WellFormed.parse_print {m : Module d} (h : m.WellFormed) :
    Fir.parse m.print = .ok m :=
  printThenParse m h

/-- Two well-formed modules that print the same text are the same module. -/
theorem Module.WellFormed.print_injective {m₁ m₂ : Module d} (h₁ : m₁.WellFormed)
    (h₂ : m₂.WellFormed) (he : m₁.print = m₂.print) : m₁ = m₂ :=
  Fir.print_injective printThenParse h₁ h₂ he

/-- Two well-formed modules print the same text exactly when they are the
same module. -/
theorem Module.WellFormed.print_inj {m₁ m₂ : Module d} (h₁ : m₁.WellFormed)
    (h₂ : m₂.WellFormed) : m₁.print = m₂.print ↔ m₁ = m₂ :=
  ⟨h₁.print_injective h₂, congrArg Module.print⟩

/-- A valid module reads back from its printed text. -/
theorem Module.Valid.parse_print {m : Module d} (h : m.Valid) : Fir.parse m.print = .ok m :=
  (validIsWellFormed m h).parse_print

/-- Two valid modules that print the same text are the same module. -/
theorem Module.Valid.print_injective {m₁ m₂ : Module d} (h₁ : m₁.Valid) (h₂ : m₂.Valid)
    (he : m₁.print = m₂.print) : m₁ = m₂ :=
  (validIsWellFormed m₁ h₁).print_injective (validIsWellFormed m₂ h₂) he

/-! # The round trip of the core dialect -/

/-- `parse(print(m)) == m` for every well-formed module of the core
dialect. -/
theorem Core.printThenParse : PrintThenParse (d := CoreDialect) Fir.parse :=
  Fir.printThenParse

/-- `print(parse(t)) == t` for every text printed from a well-formed module
of the core dialect. -/
theorem Core.parseThenPrint : ParseThenPrint (d := CoreDialect) Fir.parse :=
  Fir.parseThenPrint

/-- Two valid modules of the core dialect that print the same text are the
same module. -/
theorem Core.print_injective {m₁ m₂ : Module CoreDialect} (h₁ : m₁.Valid) (h₂ : m₂.Valid)
    (he : m₁.print = m₂.print) : m₁ = m₂ :=
  h₁.print_injective h₂ he

end Fir
