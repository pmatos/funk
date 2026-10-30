import Fir.Text.Print
import Fir.Validation.Rules

/-!
# Round trips

Two properties tie the parser to the printer (P3, ADR-2026-10-29-2014, as
refined by ADR-2026-10-30-0815):

* `parse(print(m)) == m` for every well-formed module `m`;
* `print(parse(t)) == t` for every text `t` printed from a well-formed
  module.

The second follows from the first. A module is well formed when its printed
form says everything it holds: every name, word and attribute can be written
as a token, every number is in range, and every op can be read back from its
name, its attributes and the types of its operands and results. These
conditions are syntactic. A module that is not well formed, such as one
whose op uses a value it never defines, has no text that parses back to it:
the parser rejects its printed form with a located reason, as the grammar
section says.

Validation implies well-formedness: every valid module can be written and
read back, so two different valid modules never print the same text. This
is `ValidIsWellFormed`, an obligation of every dialect. Validation checks
the names, labels, operand types, successors and location references of a
module, and the writability laws of `LawfulDialectText` cover what the
dialect writes, so the obligation holds for every lawful dialect. The
parser is written by #10. #11 proves the first property, and proves
`ValidIsWellFormed` for the core dialect.

The conditions look at every block and op of a function, at any depth: the
blocks of the regions of its ops too.
-/

namespace Fir

open Text

variable {d : Dialect}

/-- Every op of a function, at any depth. -/
def Func.allOps (f : Func d) : List (Operation d) := f.allBlocks.flatMap (·.body)

variable [DialectSignature d] [DialectText d]

/-- An op can be written, and read back from its context. -/
def Func.OpWellFormed (f : Func d) (o : Operation d) : Prop :=
  isWord (opName o.op) ∧ Attr.AllWritable (opAttrs o.op) ∧
  o.operands.map f.typeOf = (sig o.op).map some ∧
  o.results.map (·.2) = returnTypes o.op ∧
  (∀ s ∈ o.succs, isName s.label ∧ ∀ a ∈ s.args, isName a) ∧
  o.loc < Location.limit

/--
A function can be written and read back: its value names are unique and can
be written; its labels can be written; each type it states is written as a
type and decodes back to itself; and each of its ops can be written and read
back. Its symbol can be any string.
-/
structure Func.WellFormed (f : Func d) : Prop where
  namesUnique : (f.defs.map (·.1)).Nodup
  names : ∀ x ∈ f.defs, isName x.1
  labels : ∀ b ∈ f.allBlocks, isName b.label
  types : ∀ t ∈ f.types, (tyAttr t).IsType ∧ decodeTy (tyAttr t) = some t
  ops : ∀ o ∈ f.allOps, f.OpWellFormed o

/-- A module can be written and read back: each of its functions can, and
each number in its location table is in range. -/
structure Module.WellFormed (m : Module d) : Prop where
  funcs : ∀ f ∈ m.funcs, f.WellFormed
  locs : m.locs.InLimits

/-- A position in a text: a line and a column, counted as in locations.
Lines count from 1, and columns count UTF-8 bytes from 1. -/
structure TextPos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq

/-- Why a parser rejects a text, and where. The reason is for people; tools
compare only whether a text is rejected. -/
structure ParseError where
  pos : TextPos
  reason : String
  deriving Repr

/-- A parser: from text to a module, or to a located error. -/
abbrev Parser (d : Dialect) := String → Except ParseError (Module d)

/-- `parse(print(m)) == m` for every well-formed module. -/
def PrintThenParse (parse : Parser d) : Prop :=
  ∀ m : Module d, m.WellFormed → parse m.print = .ok m

/-- `print(parse(t)) == t` for every text printed from a well-formed module. -/
def ParseThenPrint (parse : Parser d) : Prop :=
  ∀ m₀ : Module d, m₀.WellFormed → ∀ m, parse m₀.print = .ok m → m.print = m₀.print

/-- The second round trip follows from the first. -/
theorem parseThenPrint_of_printThenParse {parse : Parser d}
    (h : PrintThenParse parse) : ParseThenPrint parse := by
  intro m₀ hw m hp
  rw [h m₀ hw] at hp
  cases hp
  rfl

/-- With the first round trip, two different well-formed modules never print
the same text. -/
theorem print_injective {parse : Parser d} (h : PrintThenParse parse)
    {m₁ m₂ : Module d} (h₁ : m₁.WellFormed) (h₂ : m₂.WellFormed)
    (he : m₁.print = m₂.print) : m₁ = m₂ := by
  have e₁ := h m₁ h₁
  rw [he, h m₂ h₂] at e₁
  cases e₁
  rfl

/-- Every valid module of the dialect is well formed: an obligation of every
dialect, which the writability laws of `LawfulDialectText` make hold. #11
proves it for the core dialect. -/
def ValidIsWellFormed [DialectValidation d] : Prop :=
  ∀ m : Module d, m.Valid → m.WellFormed

end Fir
