import Std.Data.HashMap
import Fir.Text.ReadLocs

/-!
The last step decodes what the grammar leaves generic, through the dialect's
`DialectText` instance. Each item is decoded from its kind, each type with
`decodeTy`, and each op with `decodeOp`, from its name, its attributes and
the types of its operands and results. The types of the operands are found
where the values are defined, so a function is decoded in two passes. The
first reads every definition of the function, at any depth, and builds its
_scope_: each value it defines, with its type. The second decodes each op
in that scope.

A text that follows the grammar but does not decode is rejected, with the
position of the part that does not decode (ADR-2026-10-30-0815):

* an item whose kind is not `func`, at its kind; a `func` with attributes, at
  its first attribute; and a `func` whose body holds items, at the first;
* a type that does not decode, at the type;
* a value defined twice, at its second definition;
* an operand that its function does not define, at the operand;
* an op that does not decode, at its name.

A location reference, line or column out of range, and a string or symbol
not in its one spelling, are rejected by the earlier steps, where they
stand. A width or a constant out of its range is a type or an op that does
not decode. A successor argument needs no type to decode its op, so one
that the function does not define is left to validation.

The first pass checks the function's result types, then its parameters,
then its blocks in order: each block's arguments, then each op's results and
the blocks of its regions. So a text with several errors is rejected at the
first of them in that order. `funk` follows the same order, except that it
rejects an op whose name no dialect has before it looks up the op's
operands; `decodeOp` takes the name, the attributes and the types together,
so this parser looks up the operands first.
-/

namespace Fir.Text

variable {d : Dialect} [DialectText d]

/-- The values a function defines, with their types. -/
abbrev Scope (d : Dialect) := Std.HashMap Name d.Ty

/-- Decodes a type written at `p`. -/
def decodeType (a : Attr) (p : TextPos) : Except ParseError d.Ty :=
  match decodeTy a with
  | some t => .ok t
  | none => errorAt p ("type " ++ a.print ++ " does not decode")

/-- Decodes a definition: its value and its type. -/
def decodeDef (x : SDef) : Except ParseError (Name × d.Ty) := do
  pure (x.name, ← decodeType x.ty x.tyPos)

/-- Adds definitions to the scope. A value already in it is defined twice. -/
def define (sc : Scope d) : List SDef → Except ParseError (Scope d)
  | [] => pure sc
  | x :: xs => do
    let (n, t) ← decodeDef x
    if sc.contains n then errorAt x.pos ("value %" ++ n ++ " is defined twice")
    else define (sc.insert n t) xs

mutual
/-- Adds the definitions of these blocks, at any depth, to the scope. -/
def defineBlocks (sc : Scope d) : List SBlock → Except ParseError (Scope d)
  | [] => pure sc
  | ⟨_, params, ops⟩ :: bs => do
    let sc ← define sc params
    let sc ← defineOps sc ops
    defineBlocks sc bs

/-- Adds the results of these ops, and the definitions of their regions, to
the scope. -/
def defineOps (sc : Scope d) : List SOp → Except ParseError (Scope d)
  | [] => pure sc
  | ⟨results, _, _, _, _, _, regions, _⟩ :: os => do
    let sc ← define sc results
    let sc ← defineRegions sc regions
    defineOps sc os

/-- Adds the definitions of the blocks of these regions to the scope. -/
def defineRegions (sc : Scope d) : List SRegion → Except ParseError (Scope d)
  | [] => pure sc
  | ⟨bs⟩ :: rs => do
    let sc ← defineBlocks sc bs
    defineRegions sc rs
end

/-- The type of each operand, found in the scope. An operand that the
function `f` does not define has none. -/
def operandTypes (sc : Scope d) (f : String) : List (Name × TextPos) → Except ParseError (List d.Ty)
  | [] => pure []
  | (x, p) :: xs => match sc[x]? with
    | some t => do pure (t :: (← operandTypes sc f xs))
    | none => errorAt p ("value %" ++ x ++ " is not defined in " ++ printSymbol f)

mutual
/-- Decodes the blocks of the function `f`, in its scope. -/
def decodeBlocks (sc : Scope d) (f : String) : List SBlock → Except ParseError (List (Block d))
  | [] => pure []
  | ⟨label, params, ops⟩ :: bs => do
    let params ← params.mapM decodeDef
    let ops ← decodeOps sc f ops
    pure (⟨label, params, ops⟩ :: (← decodeBlocks sc f bs))

/-- Decodes ops of the function `f`, in its scope. -/
def decodeOps (sc : Scope d) (f : String) : List SOp → Except ParseError (List (Operation d))
  | [] => pure []
  | ⟨results, name, namePos, attrs, operands, succs, regions, loc⟩ :: os => do
    let ts ← operandTypes sc f operands
    let results ← results.mapM decodeDef
    match decodeOp name attrs ts (results.map (·.2)) with
    | none => errorAt namePos ("op " ++ name ++ " does not decode: the dialect has no op " ++
        "with this name and these attributes, operand types and result types")
    | some op => do
      let regions ← decodeRegions sc f regions
      let o : Operation d := ⟨results, op, operands.map (·.1), succs, regions, loc⟩
      pure (o :: (← decodeOps sc f os))

/-- Decodes the regions of an op of the function `f`, in its scope. -/
def decodeRegions (sc : Scope d) (f : String) : List SRegion → Except ParseError (List (Region d))
  | [] => pure []
  | ⟨bs⟩ :: rs => do pure (⟨← decodeBlocks sc f bs⟩ :: (← decodeRegions sc f rs))
end

/-- Decodes a function: its result types and its definitions first, then
its ops. -/
def decodeFunc (name : String) (params : List SDef) (results : List (Attr × TextPos))
    (blocks : List SBlock) : Except ParseError (Func d) := do
  let results ← results.mapM fun (a, p) => decodeType a p
  let sc ← define ∅ params
  let sc ← defineBlocks sc blocks
  let params ← params.mapM decodeDef
  pure ⟨name, params, results, ⟨← decodeBlocks sc name blocks⟩⟩

/-- Decodes an item. In M0 every item is a `func`, with no attributes and
with blocks in its body. -/
def decodeItem : SItem → Except ParseError (Item d)
  | ⟨kind, kindPos, name, params, results, attrs, body⟩ =>
    if kind ≠ "func" then errorAt kindPos ("unknown item kind " ++ kind ++ ": M0 has only func")
    else match attrs, body with
      | (_, p) :: _, _ => errorAt p "a func has no attributes"
      | [], .items (⟨_, p, _, _, _, _, _⟩ :: _) => errorAt p "a func's body holds blocks, not items"
      | [], .items [] => do pure (.func (← decodeFunc name params results []))
      | [], .blocks bs => do pure (.func (← decodeFunc name params results bs))

/-- Decodes a module. -/
def decodeModule (m : SModule) : Except ParseError (Module d) := do
  pure ⟨← m.items.mapM decodeItem, m.locs⟩

end Fir.Text

namespace Fir

/--
The parser: from text to a module of the dialect `d`, or to the first error
with its position. It reads the tokens, then the grammar, then decodes.
-/
def parse {d : Dialect} [DialectText d] : Parser d := fun text => do
  let tokens ← Text.lex text
  let tree ← Text.readModule tokens
  Text.decodeModule tree

end Fir
