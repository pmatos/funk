import Fir.Text.DecodeAcceptedModule
import Fir.Text.PrintParse

/-!
# The parser gives well-formed modules

Every module that the parser gives is well formed, for every dialect whose
text is lawful: `parse_wellFormed` joins the three steps of the sections
before this one. The lexer reads only tokens that can be written
(`lex_writable`), the grammar reads them into a tree that can be written
(`readModule_writable`), and a tree that can be written decodes to a
well-formed module (`decodeModule_wellFormed`). It holds for every text
that the parser accepts, not only for the texts that the printer writes:
a text with comments, with other spacing or without its final line feed,
or one that another tool wrote.

With the round trip, `printThenParse`, the printed form of every module
that the parser gives reads back as that module
(`parse_print_of_parse`). So printing what the parser reads is idempotent
on every text that the parser accepts: formatting a text and formatting
the result again give the same text. Both hold for the core dialect, with
`Core.lawfulDialectText` (`Core.parse_wellFormed`,
`Core.parse_print_of_parse`).

# What each field rests on

Each field of `Module.WellFormed` is a check that the parser makes. The
lexer's step, the grammar's step and the two passes of decoding carry it
from the text to the module. Of each function, `Func.WellFormed` asks:

* `namesUnique`, that each value is defined once: the first pass of
  decoding, `define`, rejects a value already in the function's scope, and
  it reads every definition of the function, at any depth (`define_holds`,
  `SBlock.adds`).
* `names`, that each value's name is a name: the lexer reads a value as `%`
  and one or more name characters (`lexToken_writable`), and a definition's
  name is a value token: `readDef` takes it from one, and so does
  `readOps` for an op's first result (`readDef_writable`,
  `readBlocks_writable`).
* `labels`, that each label is a name: the lexer reads a label as `^` and
  one or more name characters, and `readBlocks` takes a block's label from
  a label token.
* `types`, that each type is written as a type and decodes back to itself:
  `readType` reads only a word, or a word applied to attributes, and the
  lexer's words are words (`readType_writable`, `readAttr_writable`).
  `decodeType` gives `decodeTy a = some t`, and the law `encode_decodeTy`
  gives `tyAttr t = a` (`decodeType_writable`).
* `ops`, that each op, at any depth, can be written and read back
  (`Func.OpWellFormed`):
  * its name is a word: `readOps` and `readOpWithResults` take it from a
    word token, and the law `encode_decodeOp` makes it `opName` of the op
    instance;
  * its attributes can be written: `readAttrs` reads them from tokens that
    can be written (`readAttrs_writable`), and `encode_decodeOp` makes them
    `opAttrs`;
  * its operands have the types of `sig`: `operandTypes` finds each operand
    in the scope, which gives each value the type that `Func.typeOf` gives
    it, and `encode_decodeOp` makes the types that `decodeOp` was given
    `sig` of the op instance;
  * its results have the types of `returnTypes`: `decodeOp` is given the
    types of the op's results, and `encode_decodeOp` makes them
    `returnTypes`;
  * its successors' labels and arguments are names: `readSucc` and
    `readSuccArgs` take them from label and value tokens;
  * its location reference is below `2^32`: `readOpLoc` takes it from a
    location reference token, and `lexAt` rejects a reference of `2^32` or
    more.

Of the module, `Module.WellFormed` also asks `locs`, that every number of
its location table is below `2^32`: its references come from location
reference tokens, and `readNat` rejects a line or a column of `2^32` or
more (`readLocs_writable`).

So the parser has a check for every field, and no text that it accepts
gives a module that is not well formed. A change to the parser that drops
one of these checks breaks this proof, at the step that made the check.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectSignature d] [DialectValidation d] [DialectText d]
  [LawfulDialectText d]

/-- Every module that the parser gives is well formed, for every dialect
whose text is lawful. -/
theorem parse_wellFormed {t : String} {m : Module d} (h : Fir.parse t = .ok m) :
    m.WellFormed := by
  unfold Fir.parse at h
  bind_step h with ⟨ts, h₁, h⟩
  bind_step h with ⟨s, h₂, h₃⟩
  exact decodeModule_wellFormed h₃ (readModule_writable h₂ (lex_writable h₁))

/-- The printed form of every module that the parser gives reads back as
that module: printing what the parser reads is idempotent on every text
that it accepts. -/
theorem parse_print_of_parse {t : String} {m : Module d} (h : Fir.parse t = .ok m) :
    Fir.parse m.print = .ok m :=
  (parse_wellFormed h).parse_print

/-! # Parsing modules of the core dialect -/

/-- Every module of the core dialect that the parser gives is well
formed. -/
theorem Core.parse_wellFormed {t : String} {m : Module CoreDialect}
    (h : Fir.parse t = .ok m) : m.WellFormed :=
  Fir.parse_wellFormed h

/-- The printed form of every module of the core dialect that the parser
gives reads back as that module. -/
theorem Core.parse_print_of_parse {t : String} {m : Module CoreDialect}
    (h : Fir.parse t = .ok m) : Fir.parse m.print = .ok m :=
  Fir.parse_print_of_parse h

end Fir
