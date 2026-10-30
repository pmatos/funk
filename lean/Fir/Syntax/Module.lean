import Fir.Syntax.Dialect
import Fir.Syntax.Location

/-!
A module holds functions. A function is a control-flow graph of blocks (E0,
ADR-2026-10-29-2005). A block declares typed arguments and holds a list of
ops that ends with a terminator. Every op has the same shape, whatever its
dialect (G0): results, an op instance of its dialect, operands, successors,
regions and a location reference.

The terms are extrinsically typed. Values are referred to by name, and the
names are stored as the producer wrote them (P3, ADR-2026-10-29-2014). Typing,
scoping and dominance are rules of the validation chapter, not of these
types: a term can be ill-formed, and validation says which terms are valid.
-/

namespace Fir

/--
A name, without its sigil: a value `%x`, a block label `^loop` or a symbol
`@f` is stored as `x`, `loop` or `f`.
-/
abbrev Name := String

/-!
# Names

A value name or a block label is one or more _name characters_: ASCII
letters, digits, `_` and `.`, so `0` and `acc.1` are names. A _word_ is a
name that starts with a letter or `_`. Validation requires every value name
and label of a function to be a name, so that the text can write it. A
symbol may be any string: the text writes it bare when it is a word, and
quoted otherwise.
-/

/-- An ASCII letter. -/
def isLetter (c : Char) : Bool := ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

/-- A character that may start a word. -/
def isWordStart (c : Char) : Bool := isLetter c ∨ c = '_'

/-- A name character: a letter, a digit, `_` or `.`. -/
def isNameChar (c : Char) : Bool := isWordStart c ∨ c.isDigit ∨ c = '.'

/-- A valid value name or block label: one or more name characters. -/
def isName (s : String) : Bool := !s.isEmpty && s.all isNameChar

/-- A word: a name that starts with a letter or `_`. -/
def isWord (s : String) : Bool :=
  match s.toList with
  | c :: cs => isWordStart c && cs.all isNameChar
  | [] => false

/--
A successor of a terminator: the block that control may go to, and the
values passed to that block's arguments (H1, ADR-2026-10-29-2010).
-/
structure Succ where
  /-- The label of the target block. -/
  label : Name
  /-- One value for each argument of the target block. -/
  args : List Name
  deriving Repr, DecidableEq

mutual
/--
An op in place, in a block: one operation of fir.

* `results` names each result and gives its type.
* `op` is the op instance of the dialect: the op's name, its attributes and
  the types it is used at.
* `operands` are the values the op uses.
* `succs` are the op's successors. Only terminators have them.
* `regions` are the regions the op owns. No op of the core dialect has one,
  so in M0 this list is always empty; it is part of every op so that a
  dialect with regions needs no new syntax (G0).
* `loc` is the op's required location, as a reference into the module's
  location table (H8).
-/
structure Operation (d : Dialect) where
  results : List (Name × d.Ty)
  op : d.Op
  operands : List Name
  succs : List Succ
  regions : List (Region d)
  loc : LocRef

/--
A block: a label, typed arguments, and a list of ops whose last op is the
block's terminator.
-/
structure Block (d : Dialect) where
  label : Name
  params : List (Name × d.Ty)
  body : List (Operation d)

/--
A region: a list of blocks. The first block is the region's entry.
-/
structure Region (d : Dialect) where
  blocks : List (Block d)
end

/--
A function: a region isolated from above (H2, ADR-2026-10-29-2011). Nothing
in it refers to a value outside it, and it reaches other functions only by
symbol (H3, ADR-2026-10-29-2012).

`params` are the function's parameters. They are the arguments of the
entry block, the first block of `body`, which declares none of its own.
`results` are the types the function returns: any number of them, none
included (ADR-2026-10-30-0816).
-/
structure Func (d : Dialect) where
  name : Name
  params : List (Name × d.Ty)
  results : List d.Ty
  body : Region d

/--
An item of a module. In M0 every item is a function.

A module is a symbol table, and G0 requires that symbol tables can nest, for
example a device module inside a host module. A nested module, a global or
an external declaration would each be a new kind of item, and a new
constructor here. The text format already writes every item with one
generic production (N2), so a new kind needs no grammar change. How
dialects and extensions add kinds of item is H4 and H5, which are not
decided, so M0 defines only functions.
-/
inductive Item (d : Dialect) where
  | func (f : Func d)

/--
A module: its items, then its location table. In text the table ends the
module.
-/
structure Module (d : Dialect) where
  items : List (Item d)
  locs : LocTable

/-- The functions of a module, in order. -/
def Module.funcs (m : Module d) : List (Func d) :=
  m.items.map fun | .func f => f

end Fir
