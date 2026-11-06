import Fir.Text.DecodeAcceptedModule
import Fir.Text.PrintParse

/-!
# The parser gives well-formed modules

Every module that the parser gives is well formed, for every dialect whose
text is lawful: this section joins the three steps of the sections before
it. The lexer reads only tokens that can be written, the grammar reads them
into a tree that can be written, and a tree that can be written decodes to
a well-formed module. It holds for every text that the parser accepts, not
only for the texts that the printer writes: a text with comments, with
other spacing or without its final line feed, or one that another tool
wrote.

With the round trip, the printed form of every module that the parser
gives reads back as that module. So printing what the parser reads is
idempotent on every text that the parser accepts: formatting a text and
formatting the result again give the same text. Both hold for the core
dialect, whose text is lawful.

# What each field rests on

Each condition of a well-formed module is a check that the parser makes.
The lexer's step, the grammar's step and the two passes of decoding carry
it from the text to the module. Of each function, a well-formed module
asks:

* that each value is defined once: the first pass of decoding rejects a
  value already in the function's scope, and it reads every definition of
  the function, at any depth;
* that each value's name is a name: the lexer reads a value as `%` and one
  or more name characters, and a definition's name comes from a value
  token, both when the reader of definitions reads it and when the reader
  of ops reads an op's first result;
* that each label is a name: the lexer reads a label as `^` and one or more
  name characters, and the reader of blocks takes a block's label from a
  label token;
* that each type is written as a type and decodes back to itself: the
  reader of types reads only a word, or a word applied to attributes, and
  the lexer's words are words. The type is decoded from that attribute, and
  the law of a lawful text for types makes the attribute the one that the
  dialect writes for the type;
* that each op, at any depth, can be written and read back:
  * its name is a word: the readers of ops take it from a word token, and
    the law of a lawful text for ops makes it the name of the op instance;
  * its attributes can be written: the reader of attributes reads them
    from tokens that can be written, and the same law makes them the
    attributes of the op instance;
  * its operands have the types of the op instance's signature: the second
    pass finds each operand in the scope, which gives each value the type
    that the function gives it, and the same law makes the types that the
    dialect was given the op instance's operand types;
  * its results have the op instance's result types: the dialect is given
    the types of the op's results, and the same law makes them the op
    instance's result types;
  * its successors' labels and arguments are names: the readers of
    successors take them from label and value tokens;
  * its location reference is below `2^32`: the reader of an op takes it
    from a location reference token, and the lexer rejects a reference of
    `2^32` or more.

Of the module, a well-formed module also asks that every number of its
location table be below `2^32`: its references come from location
reference tokens, and the reader of a line or a column rejects one of
`2^32` or more.

So the parser has a check for every condition, and no text that it accepts
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
