import Fir.Syntax.Module
import Fir.Text.Lexical

/-!
# The grammar of a module

One grammar covers every op of every dialect (G0). It has no production for
any particular op: an op is always its results, its name, its attributes, its
operands, its successors, its regions and its location reference, in that
order. Types and attributes are written as generic terms. A new dialect adds
op names, types and attributes, and needs no change to this grammar or to the
parser.

```
module   ::= item* locs
item     ::= func
func     ::= 'func' symbol '(' defs? ')' ('->' types)? '{' block* '}'
block    ::= label ('(' defs ')')? ':' op*
op       ::= (defs '=')? word attr* operands? region* locref
operands ::= value (',' value)* (',' succ)* | succ (',' succ)*
succ     ::= label ('(' value (',' value)* ')')?
region   ::= '{' block* '}'
defs     ::= value ':' type (',' value ':' type)*
types    ::= type (',' type)*
type     ::= word | word '(' attr (',' attr)* ')'
attr     ::= word | int | string | symbol | word '(' attr (',' attr)* ')'
locs     ::= 'locs' '{' (locref '=' location)* '}'
location ::= 'unknown'
           | string ':' nat ':' nat '-' nat ':' nat
           | 'name' '(' string ')'
           | 'callsite' '(' locref 'at' locref ')'
           | 'fused' '(' (locref (',' locref)*)? ')'
           | 'derived' '(' locref ')'
```

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
  The one exception is a function's parameter list, whose parentheses are
  always written.

The grammar accepts some modules that validation rejects, such as a function
without blocks or a `fused` location of one entry. That keeps printing total:
every module has a printed form.

# Ops and types in text

A dialect says how its op instances and types are written. An op instance is
written as its name and attributes. Its operand and result types are not
repeated on the op: they are the types written where its operands and results
are defined. So reading an op back needs those types, and `decodeOp` takes
them. A parser first collects the type of every value a function defines,
then decodes each op from its name, its attributes, the types of its operands
and the types of its results.
-/

namespace Fir

/--
An attribute, or a type, as written in text: a word such as `nsw` or `i32`,
an integer, a string, a symbol reference such as `@sum`, or a word applied to
attributes, such as `vec(4, i32)`. The core dialect does not use the applied
form; it is there so that other dialects can write structured attributes and
types without a change to the grammar.
-/
inductive Attr where
  | word (w : String)
  | int (i : Int)
  | str (s : String)
  | sym (s : String)
  | app (head : String) (args : List Attr)
  deriving Repr, Inhabited

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
spelling. The round-trip theorem of #11 rests on them, for every dialect.
-/
class LawfulDialectText (d : Dialect) [DialectSignature d] [DialectText d] : Prop where
  decodeOp_encode : ∀ op : d.Op,
    decodeOp (opName op) (opAttrs op) (sig op) (returnTypes op) = some op
  encode_decodeOp : ∀ n as ts rs (op : d.Op), decodeOp n as ts rs = some op →
    opName op = n ∧ opAttrs op = as ∧ sig op = ts ∧ returnTypes op = rs
  decodeTy_encode : ∀ t : d.Ty, decodeTy (tyAttr t) = some t
  encode_decodeTy : ∀ a (t : d.Ty), decodeTy a = some t → tyAttr t = a

end Fir
