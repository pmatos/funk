import Fir.Text.Lex

/-!
The second step reads the tokens by the grammar of a module into a syntax
tree. The tree has no node for any particular op or kind of item, as the
grammar has none (G0): an item is its kind, symbol, parameters, results,
attributes and body, and an op is its results, name, attributes, operands,
successors, regions and location reference. Types and attributes stay
generic terms, as the grammar writes them. The tree keeps the position of
each part that decoding can reject: an item's kind and attributes, a type, a
definition, an op's name and each operand.

Location tables have a fixed syntax, so they are read in full, in the next
section, with the module that they end.

Each reader takes the tokens that are left, and returns what it read and the
tokens after it. Those are a suffix of what it was given, never more, so the
readers that call one another for nested attributes, regions and items
always end. A reader that finds a token it does not expect fails there,
naming what it expected.
-/

namespace Fir.Text

/-- A definition as written, `%x: T`: the value's name and position, and
its type as written, with the type's position. -/
structure SDef where
  name : Name
  pos : TextPos
  ty : Attr
  tyPos : TextPos

mutual
/-- An op as written, before it is decoded. -/
structure SOp where
  results : List SDef
  name : String
  namePos : TextPos
  attrs : List Attr
  operands : List (Name × TextPos)
  succs : List Succ
  regions : List SRegion
  loc : LocRef

/-- A block as written. -/
structure SBlock where
  label : Name
  params : List SDef
  ops : List SOp

/-- A region as written. -/
structure SRegion where
  blocks : List SBlock
end

mutual
/-- An item as written: `kind @sym(params) -> results attrs { body }`. -/
structure SItem where
  kind : String
  kindPos : TextPos
  name : String
  params : List SDef
  results : List (Attr × TextPos)
  attrs : List (Attr × TextPos)
  body : SBody

/-- The body of an item: blocks, or items. An empty body is no blocks. -/
inductive SBody where
  | blocks (bs : List SBlock)
  | items (is : List SItem)
end

/-- A module as written: its items, then its location table. -/
structure SModule where
  items : List SItem
  locs : LocTable

/-- The tokens after what a reader read: a suffix of the tokens it was
given, so never more. -/
abbrev After (ts : List Token) := { r : List Token // r.length ≤ ts.length }

/-- What a reader of `ts` returns: what it read and the tokens after it, or
the first error. -/
abbrev Read (α : Type) (ts : List Token) := Except ParseError (α × After ts)

/-- What a reader of `ts` that reads at least one token returns. -/
abbrev Read1 (α : Type) (ts : List Token) :=
  Except ParseError (α × { r : List Token // r.length < ts.length })

/-- Nothing read. -/
def After.here (ts : List Token) : After ts := ⟨ts, Nat.le_refl _⟩

/-- What follows `t :: ts` when `a` follows `ts`. -/
def After.next {t : Token} {ts : List Token} (a : After ts) : After (t :: ts) :=
  ⟨a.1, Nat.le_succ_of_le a.2⟩

/-- What a second reader leaves, after a first one. -/
def After.then {ts : List Token} (a : After ts) (b : After a.1) : After ts :=
  ⟨b.1, Nat.le_trans b.2 a.2⟩

/-- An error at the first token of `ts`, which names what the reader
expected there and what it found. The lexer ends every list of tokens with
`eof`, so a reader never sees an empty one. -/
def fail (ts : List Token) (expected : String) : Except ParseError α :=
  match ts with
  | t :: _ => .error ⟨t.pos, "expected " ++ expected ++ ", found " ++ t.tok.describe⟩
  | [] => .error ⟨⟨1, 1⟩, "expected " ++ expected ++ ", found the end of the text"⟩

/-- Reads the token `tok`. -/
def expect (tok : Tok) (expected : String) : (ts : List Token) → Read Unit ts
  | t :: rest => if t.tok = tok then .ok ((), ⟨rest, Nat.le_succ _⟩) else fail (t :: rest) expected
  | [] => fail [] expected

/-- Reads the word `kw`. -/
def keyword (kw : String) (ts : List Token) : Read Unit ts :=
  expect (.word kw) ("`" ++ kw ++ "`") ts

/-!
# Attributes and types
-/

mutual
/-- Reads an attribute: a word, an integer, a string, a symbol, or a word
applied to attributes. -/
def readAttr : (ts : List Token) → Read1 Attr ts
  | ⟨.word w, _⟩ :: ⟨.lparen, _⟩ :: rest => do
    let (args, ⟨r, hr⟩) ← readAttrArgs rest
    pure (.app w args, ⟨r, by simp; omega⟩)
  | ⟨.word w, _⟩ :: rest => .ok (.word w, ⟨rest, Nat.lt_succ_self _⟩)
  | ⟨.int i, _⟩ :: rest => .ok (.int i, ⟨rest, Nat.lt_succ_self _⟩)
  | ⟨.str s, _⟩ :: rest => .ok (.str s, ⟨rest, Nat.lt_succ_self _⟩)
  | ⟨.sym s, _⟩ :: rest => .ok (.sym s, ⟨rest, Nat.lt_succ_self _⟩)
  | ts => fail ts "an attribute"
termination_by ts => 2 * ts.length

/-- Reads the arguments of an applied attribute or type, after its `(`,
through its `)`. -/
def readAttrArgs : (ts : List Token) → Read (List Attr) ts
  | ⟨.rparen, _⟩ :: rest => .ok ([], ⟨rest, Nat.le_succ _⟩)
  | ts => do
    let (a, ⟨r, hr⟩) ← readAttr ts
    let (as, ⟨r', hr'⟩) ← readMoreAttrArgs r
    pure (a :: as, ⟨r', by omega⟩)
termination_by ts => 2 * ts.length + 1

/-- Reads `, attr` until the `)` that ends the arguments. -/
def readMoreAttrArgs : (ts : List Token) → Read (List Attr) ts
  | ⟨.comma, _⟩ :: rest => do
    let (a, ⟨r, hr⟩) ← readAttr rest
    let (as, ⟨r', hr'⟩) ← readMoreAttrArgs r
    pure (a :: as, ⟨r', by simp; omega⟩)
  | ⟨.rparen, _⟩ :: rest => .ok ([], ⟨rest, Nat.le_succ _⟩)
  | ts => fail ts ", or ) in the attribute's arguments"
termination_by ts => 2 * ts.length
end

/-- Reads a type: a word, or a word applied to attributes. -/
def readType : (ts : List Token) → Read (Attr × TextPos) ts
  | ⟨.word w, p⟩ :: ⟨.lparen, _⟩ :: rest => do
    let (args, ⟨r, hr⟩) ← readAttrArgs rest
    pure ((.app w args, p), ⟨r, by simp; omega⟩)
  | ⟨.word w, p⟩ :: rest => .ok ((.word w, p), ⟨rest, Nat.le_succ _⟩)
  | ts => fail ts "a type"

/-- Reads `, type` as long as a comma follows. -/
def readMoreTypes : (ts : List Token) → Read (List (Attr × TextPos)) ts
  | ⟨.comma, _⟩ :: rest => do
    let (t, ⟨r, hr⟩) ← readType rest
    let (ts', ⟨r', hr'⟩) ← readMoreTypes r
    pure (t :: ts', ⟨r', by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => ts.length

/-- Whether a token starts an attribute. -/
def Tok.startsAttr : Tok → Bool
  | .word _ | .int _ | .str _ | .sym _ => true
  | _ => false

/-- Reads attributes, each with its position, as long as one follows. -/
def readAttrs : (ts : List Token) → Read (List (Attr × TextPos)) ts
  | t :: rest =>
    if t.tok.startsAttr then do
      let (a, ⟨r, hr⟩) ← readAttr (t :: rest)
      let (as, ⟨r', hr'⟩) ← readAttrs r
      pure ((a, t.pos) :: as, ⟨r', by omega⟩)
    else .ok ([], .here _)
  | [] => .ok ([], .here _)
termination_by ts => ts.length

/-!
# Definitions, operands and successors
-/

/-- Reads the type of a definition of the value `n` at `p`, after the
value. -/
def readDefType (n : Name) (p : TextPos) (ts : List Token) : Read SDef ts := do
  let ((), a) ← expect .colon ": and the value's type" ts
  let ((ty, tp), b) ← readType a.1
  pure (⟨n, p, ty, tp⟩, a.then b)

/-- Reads `, %x: T` as long as a comma follows. -/
def readMoreDefs : (ts : List Token) → Read (List SDef) ts
  | ⟨.comma, _⟩ :: ⟨.value n, p⟩ :: rest => do
    let (d, ⟨r, hr⟩) ← readDefType n p rest
    let (ds, ⟨r', hr'⟩) ← readMoreDefs r
    pure (d :: ds, ⟨r', by simp; omega⟩)
  | ⟨.comma, _⟩ :: rest => fail rest "a value definition, `%x: type`"
  | ts => .ok ([], .here ts)
termination_by ts => ts.length

/-- Reads one or more definitions, separated by commas. -/
def readDefs : (ts : List Token) → Read (List SDef) ts
  | ⟨.value n, p⟩ :: rest => do
    let (d, a) ← readDefType n p rest
    let (ds, b) ← readMoreDefs a.1
    pure (d :: ds, (a.then b).next)
  | ts => fail ts "a value definition, `%x: type`"

/-- Reads the values passed to a successor, after its `(`, through its
`)`. -/
def readSuccArgs : (ts : List Token) → Read (List Name) ts
  | ⟨.value v, _⟩ :: ⟨.comma, _⟩ :: rest => do
    let (vs, ⟨r, hr⟩) ← readSuccArgs rest
    pure (v :: vs, ⟨r, by simp; omega⟩)
  | ⟨.value v, _⟩ :: rest => do
    let ((), a) ← expect .rparen ", or ) after the successor's arguments" rest
    pure ([v], a.next)
  | ts => fail ts "a value passed to the successor"
termination_by ts => ts.length

/-- Reads a successor: a label, with the values it passes in parentheses
when there are any. -/
def readSucc : (ts : List Token) → Read Succ ts
  | ⟨.label l, _⟩ :: ⟨.lparen, _⟩ :: rest => do
    let (args, ⟨r, hr⟩) ← readSuccArgs rest
    pure (⟨l, args⟩, ⟨r, by simp; omega⟩)
  | ⟨.label l, _⟩ :: rest => .ok (⟨l, []⟩, ⟨rest, Nat.le_succ _⟩)
  | ts => fail ts "a successor, such as ^next"

/-- Reads `, ^succ` as long as a comma follows. -/
def readMoreSuccs : (ts : List Token) → Read (List Succ) ts
  | ⟨.comma, _⟩ :: rest => do
    let (s, ⟨r, hr⟩) ← readSucc rest
    let (ss, ⟨r', hr'⟩) ← readMoreSuccs r
    pure (s :: ss, ⟨r', by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => ts.length

/-- Reads `, %x` as long as a comma and a value follow, then the
successors. -/
def readMoreOperands : (ts : List Token) → Read (List (Name × TextPos) × List Succ) ts
  | ⟨.comma, _⟩ :: ⟨.value v, p⟩ :: rest => do
    let ((vs, ss), ⟨r, hr⟩) ← readMoreOperands rest
    pure (((v, p) :: vs, ss), ⟨r, by simp; omega⟩)
  | ts => do
    let (ss, a) ← readMoreSuccs ts
    pure (([], ss), a)
termination_by ts => ts.length

/-- Reads an op's operands, then its successors: values first, then labels,
separated by commas. -/
def readOperands : (ts : List Token) → Read (List (Name × TextPos) × List Succ) ts
  | ⟨.value v, p⟩ :: rest => do
    let ((vs, ss), a) ← readMoreOperands rest
    pure (((v, p) :: vs, ss), a.next)
  | ⟨.label l, p⟩ :: rest => do
    let (s, a) ← readSucc (⟨.label l, p⟩ :: rest)
    let (ss, b) ← readMoreSuccs a.1
    pure (([], s :: ss), a.then b)
  | ts => .ok (([], []), .here ts)

/-- Reads an op's location reference. -/
def readOpLoc : (ts : List Token) → Read LocRef ts
  | ⟨.locRef r, _⟩ :: rest => .ok (r, ⟨rest, Nat.le_succ _⟩)
  | ts => fail ts "the op's location reference, such as @0"

/-!
# Blocks, ops and regions
-/

mutual
/-- Reads blocks as long as a label follows. -/
def readBlocks : (ts : List Token) → Read (List SBlock) ts
  | ⟨.label l, _⟩ :: rest => do
    let (params, ⟨r₁, h₁⟩) ← (match rest with
      | ⟨.lparen, _⟩ :: rest' => do
        let (ps, a) ← readDefs rest'
        let ((), b) ← expect .rparen ", or ) after the block's arguments" a.1
        pure (ps, (a.then b).next)
      | rest' => pure ([], .here rest') : Read (List SDef) rest)
    let ((), ⟨r₂, h₂⟩) ← expect .colon ": after the block's label" r₁
    let (ops, ⟨r₃, h₃⟩) ← readOps r₂
    let (bs, ⟨r₄, h₄⟩) ← readBlocks r₃
    pure (⟨l, params, ops⟩ :: bs, ⟨r₄, by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => 2 * ts.length

/-- Reads ops as long as one follows: an op starts with its results or its
name. -/
def readOps : (ts : List Token) → Read (List SOp) ts
  | ⟨.value n, p⟩ :: rest => do
    let (o, ⟨r, hr⟩) ← readOpWithResults n p rest
    let (os, ⟨r', hr'⟩) ← readOps r
    pure (o :: os, ⟨r', by simp; omega⟩)
  | ⟨.word w, p⟩ :: rest => do
    let (o, ⟨r, hr⟩) ← readOpBody [] w p rest
    let (os, ⟨r', hr'⟩) ← readOps r
    pure (o :: os, ⟨r', by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => 2 * ts.length

/-- Reads an op whose first result is the value `n` at `p`, after that
value. -/
def readOpWithResults (n : Name) (p : TextPos) (ts : List Token) : Read SOp ts := do
  let (d, ⟨r₁, h₁⟩) ← readDefType n p ts
  let (ds, ⟨r₂, h₂⟩) ← readMoreDefs r₁
  match h : r₂ with
  | ⟨.eq, _⟩ :: ⟨.word w, wp⟩ :: rest => do
    let (o, ⟨r, hr⟩) ← readOpBody (d :: ds) w wp rest
    pure (o, ⟨r, by subst h; simp at h₂; omega⟩)
  | ⟨.eq, _⟩ :: rest => fail rest "an op name"
  | _ => fail r₂ "= after the op's results"
termination_by 2 * ts.length
decreasing_by all_goals (simp_wf; subst_vars; simp only [List.length_cons] at *; omega)

/-- Reads the rest of an op whose results and name are read: its
attributes, operands and successors, regions and location reference. -/
def readOpBody (results : List SDef) (name : String) (namePos : TextPos) (ts : List Token) :
    Read SOp ts := do
  let (attrs, ⟨r₁, h₁⟩) ← readAttrs ts
  let ((operands, succs), ⟨r₂, h₂⟩) ← readOperands r₁
  let (regions, ⟨r₃, h₃⟩) ← readRegions r₂
  let (loc, ⟨r₄, h₄⟩) ← readOpLoc r₃
  pure (⟨results, name, namePos, attrs.map (·.1), operands, succs, regions, loc⟩, ⟨r₄, by omega⟩)
termination_by 2 * ts.length + 1

/-- Reads an op's regions, as long as a `{` follows. -/
def readRegions : (ts : List Token) → Read (List SRegion) ts
  | ⟨.lbrace, _⟩ :: rest => do
    let (bs, ⟨r₁, h₁⟩) ← readBlocks rest
    let ((), ⟨r₂, h₂⟩) ← expect .rbrace "a block or } to close the region" r₁
    let (rs, ⟨r₃, h₃⟩) ← readRegions r₂
    pure (⟨bs⟩ :: rs, ⟨r₃, by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => 2 * ts.length
end

/-!
# Items
-/

mutual
/-- Reads items as long as a word follows. At the top of the module, the
word `locs` starts the location table instead. -/
def readItems (top : Bool) : (ts : List Token) → Read (List SItem) ts
  | ⟨.word w, p⟩ :: rest =>
    if top ∧ w = "locs" then .ok ([], .here _)
    else do
      let (i, ⟨r, hr⟩) ← readItem w p rest
      let (is, ⟨r', hr'⟩) ← readItems top r
      pure (i :: is, ⟨r', by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => 2 * ts.length

/-- Reads an item whose kind is the word `kind` at `p`, after that word. -/
def readItem (kind : String) (p : TextPos) (ts : List Token) : Read SItem ts :=
  match ts with
  | ⟨.sym name, _⟩ :: rest => do
    let ((), ⟨r₁, h₁⟩) ← expect .lparen "( and the item's parameters" rest
    let (params, ⟨r₂, h₂⟩) ← (match r₁ with
      | ⟨.rparen, p⟩ :: tl => pure ([], .here (⟨.rparen, p⟩ :: tl))
      | ts' => readDefs ts' : Read (List SDef) r₁)
    let ((), ⟨r₃, h₃⟩) ← expect .rparen ")" r₂
    let (results, ⟨r₄, h₄⟩) ← (match r₃ with
      | ⟨.arrow, _⟩ :: rest' => do
        let (t, a) ← readType rest'
        let (more, b) ← readMoreTypes a.1
        pure (t :: more, (a.then b).next)
      | ts' => pure ([], .here ts') : Read (List (Attr × TextPos)) r₃)
    let (attrs, ⟨r₅, h₅⟩) ← readAttrs r₄
    let ((), ⟨r₆, h₆⟩) ← expect .lbrace "{ and the item's body" r₅
    let (body, ⟨r₇, h₇⟩) ← (match r₆ with
      | ⟨.word w, p⟩ :: tl => do
        let (is, ⟨r, hr⟩) ← readItems false (⟨.word w, p⟩ :: tl)
        pure (SBody.items is, ⟨r, hr⟩)
      | ts' => do
        let (bs, a) ← readBlocks ts'
        pure (SBody.blocks bs, a) : Read SBody r₆)
    let ((), ⟨r₈, h₈⟩) ← expect .rbrace "} to close the item's body" r₇
    pure (⟨kind, p, name, params, results, attrs, body⟩, ⟨r₈, by simp; omega⟩)
  | ts => fail ts "the item's symbol"
termination_by 2 * ts.length + 1
decreasing_by all_goals (simp_wf; simp only [List.length_cons] at *; omega)
end

end Fir.Text
