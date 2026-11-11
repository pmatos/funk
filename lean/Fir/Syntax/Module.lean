import Fir.Syntax.Dialect
import Fir.Syntax.Location

/-!
A module holds items: functions, modules nested in it, and items of the
kinds that its dialects register. A function is a
control-flow graph of blocks (ADR-2026-10-29-2005). A block declares typed arguments and holds a list of
ops that ends with a terminator. Every op has the same shape, whatever its
dialect, so that a new dialect needs no new syntax (ADR-2026-10-29-2016):
results, an op instance of its dialect, operands, successors, regions and a
location reference.

The terms, the syntax trees of programs, carry no types. Values are
referred to by name, and the names are stored as the producer wrote them
(ADR-2026-10-29-2014). Typing, scoping and dominance are rules of the
validation chapter, not of the terms: a term can be ill-formed, and
validation says which terms are valid.

This section gives names first, then float literals and attributes, then
the terms from the inside out: a successor, an op with blocks and regions, a
function, an item of a dialect's kind, an item and a module.
-/

namespace Fir

/--
A name, without its sigil: a value `%x`, a block label `^loop` or a symbol
`@f` is stored as `x`, `loop` or `f`.
-/
abbrev Name := String

/-!
# Names

What may name a value, a label or a symbol, and which names the text
writes bare.
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

/-- A word of a dialect other than the core: a word that holds a `.`, such
as `toy.cell`. Its dialect is the part before its first `.`. -/
def isDialectWord (s : String) : Bool := isWord s && s.toList.contains '.'

/-- A word of a dialect is a word. -/
theorem isWord_of_isDialectWord {s : String} (h : isDialectWord s) : isWord s :=
  (Bool.and_eq_true _ _).mp h |>.1

/-!
# Attributes

Attributes, and types as the text writes them, are terms of one generic
shape, the same for every dialect. An op instance holds its attributes in
the dialect's own form, and an item of a dialect's kind holds them as these
terms.
-/

/-- A lowercase hexadecimal digit. -/
def Text.isHexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/--
A float literal, as written in text (ADR-2026-11-11-1438). `dec neg whole
frac exp` is a decimal: `-` when `neg`, the natural number `whole`, `.`,
the digits `frac` as they are written, and then, when `exp` is an integer,
`e` and it, as in `-1.5e-7`. `hex ds` is `0x` and the hexadecimal digits
`ds` as they are written, as in `0x7fc00000`. Leading zeros of `frac` and
of `ds` are part of the literal. Which literals spell a value of a float
type is the core dialect's rule.
-/
inductive FloatLit where
  | dec (neg : Bool) (whole : Nat) (frac : List Char) (exp : Option Int)
  | hex (digits : List Char)
  deriving Repr, DecidableEq, Inhabited

/-- A float literal that can be written: its fraction is one or more
decimal digits, and its hexadecimal digits are one or more lowercase
hexadecimal digits. -/
def FloatLit.valid : FloatLit → Bool
  | .dec _ _ frac _ => !frac.isEmpty && frac.all Char.isDigit
  | .hex ds => !ds.isEmpty && ds.all Text.isHexDigit

/--
An attribute, or a type, as written in text: a word such as `nsw` or `i32`,
an integer, a string, a symbol reference such as `@sum`, a word applied to
attributes, such as `vec(4, i32)`, or a float literal, such as `1.5` or
`0x7fc00000`. The core dialect does not use the applied form; it is there
so that other dialects can write structured attributes and types without a
change to the grammar. A word applied to no attributes, `h()`, is not the
word `h`.
-/
inductive Attr where
  | word (w : String)
  | int (i : Int)
  | str (s : String)
  | sym (s : String)
  | app (head : String) (args : List Attr)
  | float (l : FloatLit)
  deriving Inhabited

mutual
/-- How `#eval` shows an attribute: as the Lean term that builds it. It is
written out because a derived instance would be `partial`, as `Attr` holds a
list of itself, and no declaration of `lean/` is (ADR-2026-10-30-1452). -/
def Attr.repr : Attr → Nat → Std.Format
  | .word w, p => Repr.addAppParen ("Fir.Attr.word " ++ reprArg w) p
  | .int i, p => Repr.addAppParen ("Fir.Attr.int " ++ reprArg i) p
  | .str s, p => Repr.addAppParen ("Fir.Attr.str " ++ reprArg s) p
  | .sym s, p => Repr.addAppParen ("Fir.Attr.sym " ++ reprArg s) p
  | .app h args, p => Repr.addAppParen ("Fir.Attr.app " ++ reprArg h ++ " " ++
      .bracket "[" (.joinSep (Attr.reprList args) ("," ++ .line)) "]") p
  | .float l, p => Repr.addAppParen ("Fir.Attr.float " ++ reprArg l) p

/-- How `#eval` shows each attribute of a list. -/
def Attr.reprList : List Attr → List Std.Format
  | [] => []
  | a :: as => a.repr 0 :: Attr.reprList as
end

instance : Repr Attr := ⟨Attr.repr⟩

mutual
/-- An attribute can be written as a token. Every symbol can: it is quoted
when its name is not a word. -/
def Attr.Writable : Attr → Prop
  | .word w => isWord w
  | .int _ | .str _ | .sym _ => True
  | .app h args => isWord h ∧ Attr.AllWritable args
  | .float l => l.valid

/-- Every attribute of a list can be written. -/
def Attr.AllWritable : List Attr → Prop
  | [] => True
  | a :: as => a.Writable ∧ Attr.AllWritable as
end

/-!
# Terms

The terms of fir, from the inside out: a successor, an op with the blocks
and regions it may own, a function, an item and a module.
-/

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
* `regions` are the regions the op owns, of the kinds that its op instance
  states. No op of the core dialect has one; the list is part of every op
  so that a dialect with regions needs no new syntax (G0).
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
A region: its kind and a list of blocks. The first block is the region's
entry.

A region names its kind (ADR-2026-11-09-1543). No kind, `none`, is the
core's kind: a control-flow graph of blocks, whose ops run in order
(ADR-2026-10-29-2005). A dialect's kind, such as a region whose ops are
unordered, is named by a word of that dialect.
-/
structure Region (d : Dialect) where
  kind : Option Name := none
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
An item of a kind that a dialect registers (ADR-2026-11-10-2224): what the
one production of an item writes, `kind @sym(params) -> results attrs { }`,
with an empty body. Its kind is a word of the dialect, such as `toy.cell`,
never `func` or `module`, which are the core's. Its attributes are terms of
the generic shape, which the dialect's rule for the kind reads, so a new
kind needs no new syntax and no change to the parser.
-/
structure DialectItem (d : Dialect) where
  kind : Name
  name : Name
  params : List (Name × d.Ty)
  results : List d.Ty
  attrs : List Attr

/-- Every type that an item of a dialect's kind states: its parameters'
types, then its results. -/
def DialectItem.types (i : DialectItem d) : List d.Ty := i.params.map (·.2) ++ i.results

/--
An item of a module: a function, a nested module (ADR-2026-11-10-1510), or
an item of a kind that a dialect registers (ADR-2026-11-10-2224).

A module is a symbol table, and G0 requires that symbol tables can nest, for
example a device module inside a host module. A `module` item is such a
table: its symbol, its own dialect set and its items. Its set is its own,
not its parent's, and its symbols are its own: an op refers by symbol only
to an item of its own table. The text format writes every item with one
generic production (N2), so a nested module needs no new production, only
the dialect set that may start its body. An item of a dialect's kind is
written with the same production too.
-/
inductive Item (d : Dialect) where
  | func (f : Func d)
  | module (name : Name) (dialects : List Name) (items : List (Item d))
  | dialect (i : DialectItem d)

/--
A module: its dialect set, its items, then its location table. In text the
dialect set starts the module and the table ends it.

The dialect set names the dialects, other than the core, whose words the
module may write (ADR-2026-11-09-1543). The core is in every module's set
and is never named. A module that names none uses the core alone.
-/
structure Module (d : Dialect) where
  dialects : List Name := []
  items : List (Item d)
  locs : LocTable

/-- The symbol of an item. -/
def Item.name : Item d → Name
  | .func f => f.name
  | .module n .. => n
  | .dialect i => i.name

/-- The function that an item is, if it is one. -/
def Item.func? : Item d → Option (Func d)
  | .func f => some f
  | _ => none

@[simp] theorem Item.func?_func (f : Func d) : (Item.func f).func? = some f := rfl
@[simp] theorem Item.func?_module (n : Name) (ds : List Name) (is : List (Item d)) :
    (Item.module n ds is).func? = none := rfl
@[simp] theorem Item.func?_dialect (i : DialectItem d) : (Item.dialect i).func? = none := rfl

/-- The item of a dialect's kind that an item is, if it is one. -/
def Item.dialect? : Item d → Option (DialectItem d)
  | .dialect i => some i
  | _ => none

/-- The functions of a module's own table, in order. The functions of a
nested module are not among them: they are its own. -/
def Module.funcs (m : Module d) : List (Func d) :=
  m.items.filterMap Item.func?

end Fir
