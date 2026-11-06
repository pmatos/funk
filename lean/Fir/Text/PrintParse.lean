import Fir.Text.DecodeModule
import Fir.Text.ReadModule
import Fir.Core.TextLaws

/-!
# Parsing a printed module

The parser reads a text in three steps, and the proof of the round trip
has one for each. The lexer reads the printed text of a module as the
module's tokens. The grammar reads those tokens, at any positions, as the
module's tree, up to positions. Decoding gives the module back from any
tree that erases to its tree. Each step needs only part of what
well-formedness says, and a well-formed module has all of it. So
`parse(print(m)) == m` for every well-formed module `m` of every dialect
whose text is lawful: the parser meets the round trip print then parse.

The second round trip, `print(parse(t)) == t` for every text `t` printed
from a well-formed module, follows. So does injectivity: two well-formed
modules that print the same text are the same module. Every valid module
is well formed, so both hold for valid modules too. The core dialect's text
is lawful, so all of it holds for the core dialect.

# What a new dialect or a new core op needs

The proof uses nothing of a dialect but the seven laws of lawful text, so
it covers every lawful dialect at once:

* a new dialect gets the round trip by proving the laws for its own text;
* a change to the core op set, such as a new op or a new flag, extends the
  proof of the core dialect's laws, case by case.

Neither reworks the proof of the round trip. A new kind of item is a change
to the printer and the parser themselves, since it must be printed and the
decoder of items must learn to decode it, and so it extends the lemmas for
items of each step of this proof.
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
