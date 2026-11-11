import Fir.Syntax.Module
import Fir.Text.Lexical
import Fir.Validation.Scope

/-!
One grammar covers every item and every op of every dialect
(ADR-2026-10-29-2016). It has no production for any particular op: an op is
always its results, its name, its attributes, its operands, its successors,
its regions and its location reference, in that order. An item is always
its kind, its symbol, its parameters, its results, its attributes and its
body. Types and attributes are written as generic terms. So a new dialect
adds words, and needs no change to this grammar or to the parser, and so
does a kind of item that a dialect registers (ADR-2026-11-10-2224). A float
or a nested symbol reference needs new tokens: a change to the tokens of
the previous section.

* An item's kind says what it is. The core's kinds are `func` and
  `module`, so a function is written as `func @sum(%n: i32) -> i32 { ... }`
  and a nested module as `module @dev() { ... }`. A `func` has no
  attributes, and its body is its blocks. A `module` has no parameters,
  results or attributes, and its body is its items, which may start with
  its own dialect set (ADR-2026-11-10-1510). Any other kind is a word of a
  dialect, such as `toy.cell`, which that dialect registers: its item is
  written with the same production, and its attributes say what a
  function's header cannot, as in `toy.cell @c() -> toy.flag 1 { }`. Its
  body is empty. The word `locs` starts the location table, so no kind is
  named `locs`. One table ends the text, and every item refers into it,
  however deeply it is nested.
* A module's dialect set starts the text, when it names a dialect: the word
  `dialects`, then the names of the dialects, separated by commas, as in
  `dialects toy, gpu` (ADR-2026-11-10-1306). A nested module's set starts
  its body in the same way. So no kind is named `dialects` either. The core
  is in every set and is never named, and a module that names no dialect
  writes no set.
* A function's parameters are written in its header, and are the arguments
  of its entry block. The entry block, like every block, is written with its
  label, as in `^entry:`.
* An op defines its results as `%x: T`, like a block argument or a
  parameter. Every value is written with its type where it is defined, and
  with its name alone where it is used.
* An op's operands come before its successors. A successor is written with
  its label and, when its block has arguments, the values it passes.
* Empty lists are left out, never written empty: a block without arguments
  is `^body:`, not `^body():`, and a successor without arguments is `^body`.
  Three lists are the exceptions, and always have their parentheses: an
  item's parameters, the arguments of an applied attribute or type, and the
  references of a `fused` location. So `h()` and `h` are different
  attributes. Validation requires a `fused` location to fuse at least two,
  but the printer writes an empty one as `fused()`.
* A source range is written `"file":l₁:c₁ to l₂:c₂`, as MLIR writes it.

The grammar accepts some modules that validation rejects, such as a function
without blocks or a `fused` location of one entry. That keeps printing total:
every module has a printed form.

This section gives, in order: the attributes and types that the grammar
writes as generic terms, how a dialect writes its ops and types and the
laws that make them read back, and how a parser reads a text.
-/

namespace Fir

/-!
# Attributes and types

Attributes and types are terms of one generic shape, the same for every
dialect, `Attr`, which the chapter on the abstract syntax gives. A type is
one of these terms of a particular form.
-/

/-- A type is written as a word, or a word applied to attributes. -/
def Attr.IsType : Attr → Prop
  | a@(.word _) | a@(.app ..) => a.Writable
  | _ => False

/-!
# Ops and types in text

A dialect says how its op instances and types are written. An op instance
is written as its name and attributes. Its operand and result types are not
repeated on the op: they are the types written where its operands and
results are defined. So reading an op back needs those types, and the
dialect's reader of ops takes them.
-/

/--
How a dialect writes its ops and types.

* `opName` and `opAttrs` give the name and the attributes of an op instance.
* `decodeOp n as ts rs` is the op instance with name `n` and attributes `as`
  whose operand types are `ts` and whose result types are `rs`, if there is
  one.
* `tyAttr` writes a type, and `decodeTy` reads one back.
-/
class DialectText (d : Dialect) where
  opName : d.Op → String
  opAttrs : d.Op → List Attr
  decodeOp : String → List Attr → List d.Ty → List d.Ty → Option d.Op
  tyAttr : d.Ty → Attr
  decodeTy : Attr → Option d.Ty
export DialectText (opName opAttrs decodeOp tyAttr decodeTy)

/--
The laws that make a dialect's text round-trip. Decoding what was encoded
gives back the op instance or the type, and decoding succeeds only on what
encoding produces, so each op instance and each type has exactly one
spelling. Every valid type can be read back; a type that is not valid, such
as a width beyond the text's limit, may not be.

Three more laws say that what the dialect writes fits the grammar: each op
name is a word, each op's attributes can be written, and each valid type is
written as a type. With them, every valid module of the dialect is well
formed (see the round-trip section). The round-trip theorem,
`printThenParse`, rests on these laws, for every dialect.
-/
class LawfulDialectText (d : Dialect) [DialectSignature d] [DialectValidation d]
    [DialectText d] : Prop where
  decodeOp_encode : ∀ op : d.Op,
    decodeOp (opName op) (opAttrs op) (sig op) (returnTypes op) = some op
  encode_decodeOp : ∀ n as ts rs (op : d.Op), decodeOp n as ts rs = some op →
    opName op = n ∧ opAttrs op = as ∧ sig op = ts ∧ returnTypes op = rs
  decodeTy_encode : ∀ t : d.Ty, validTy t → decodeTy (tyAttr t) = some t
  encode_decodeTy : ∀ a (t : d.Ty), decodeTy a = some t → tyAttr t = a
  opName_isWord : ∀ op : d.Op, isWord (opName op)
  opAttrs_writable : ∀ op : d.Op, Attr.AllWritable (opAttrs op)
  tyAttr_isType : ∀ t : d.Ty, validTy t → (tyAttr t).IsType

/-!
# Reading a text

A parser reads a text in two steps. It first reads the text by the grammar
above. Then it decodes what the grammar leaves generic: each item from its
kind, each type through the dialect, and each op from its name, its
attributes and the types of its operands and results, which it finds where
those values are defined in the function.

A text that follows the grammar but does not decode is not a module. A parser
rejects it with a reason and the position in the text where the reason
applies (ADR-2026-10-30-0815):

* a number out of its range;
* a string or quoted symbol not in its one spelling, such as an escape the
  printer does not write, or a quoted name that is a word;
* an item whose kind the parser does not know: every kind but `func`,
  `module` and the words of dialects; a `func` with attributes, or with a
  dialect set or items in its body; a `module` with parameters, results,
  attributes or blocks; and an item of a dialect's kind with a body that is
  not empty;
* a type that does not decode;
* a value that a function defines twice: an operand's type is found at its
  definition, so each value has one;
* an operand that the function does not define, or defines in another
  function: it has no type;
* an op whose name, attributes, operand types and result types do not
  decode, such as `add` of an `i32` and an `i64`. A type mismatch is this
  kind of error.

A text that decodes is a module, and validation decides whether it is valid.
Whether a dialect registers the kind of an item of a dialect's kind is
validation's question, as whether a name is defined is: a reader decodes
such an item whatever dialects it holds.
A successor argument needs no type to decode its op, so one that the
function does not define is left to validation, like a duplicate label, a
duplicate symbol and every other rule of the validation chapter.
-/

end Fir
