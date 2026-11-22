import Std.Data.HashMap
import Fir.Text.ReadLocs
import Fir.Syntax.FuncAttrs

/-!
The last step decodes what the grammar leaves generic, through the dialect's
text. Each item is decoded from its kind, each type with the dialect's
reader of types, and each op with its reader of ops, from its name, its
attributes and the types of its operands and results. The types of the
operands are found where the values are defined, so a function is decoded
in two passes. The first reads every definition of the function, at any
depth, and builds its _scope_: each value it defines, with its type. The
second decodes each op in that scope.

A text that follows the grammar but does not decode is rejected, with the
position of the part that does not decode (ADR-2026-10-29-2014):

* an item whose kind is neither `func`, `module`, `aggregate`, `global`,
  `extern` nor a word of a dialect, at its kind. An item of a dialect's kind decodes whichever
  dialect registers it: that is validation's question (ADR-2026-11-09-1543);
* a `func` with no results and attributes, at its first attribute; a `func`
  whose body holds a dialect set, at its kind; and one whose body holds
  items, at the first;
* an external declaration whose body is not empty, at its kind, and one
  with no results and attributes, at its first attribute
  (ADR-2026-11-09-1547);
* an item other than a `func` or an `extern` whose parameter carries attributes, whose
  parameters end in `...`, or whose result before a comma carries
  attributes, at the first such attribute or at the `...`;
* a `module` with parameters, results or attributes, at the first of them,
  and one whose body holds blocks, at its kind;
* an item of a dialect's kind whose body is not empty, at its kind;
* an aggregate's layout with parameters or results, at the first of them;
  one whose body is not empty, at its kind; and one whose attributes are
  not its memory, size and alignment, then fields, at the first attribute
  that does not decode, or at its kind when it has fewer than three
  (ADR-2026-11-16-1546);
* a global with parameters or results, at the first of them; one whose body
  is not empty, at its kind; and one whose attributes do not decode, at the
  first that does not, or at its kind when it has too few
  (ADR-2026-11-09-1546);
* a type that does not decode, at the type;
* an entry of the data layout that does not decode, at the entry
  (ADR-2026-11-12-1821);
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
operands; the dialect's reader of ops takes the name, the attributes and
the types together, so this parser looks up the operands first.

This section gives the scope and the first pass, then the second pass, a
function, an item and a module, and last the parser as a whole.
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
  | ⟨_, bs⟩ :: rs => do
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
  | ⟨k, bs⟩ :: rs => do pure (⟨k, ← decodeBlocks sc f bs⟩ :: (← decodeRegions sc f rs))
end

/-- Decodes a function: its result types and its definitions first, then
its ops. A function's body is a region of the core's kind. -/
def decodeFunc (name : String) (params : List SDef) (results : List (Attr × TextPos))
    (blocks : List SBlock) : Except ParseError (Func d) := do
  let results ← results.mapM fun (a, p) => decodeType a p
  let sc ← define ∅ params
  let sc ← defineBlocks sc blocks
  let params ← params.mapM decodeDef
  pure ⟨name, params, results, ⟨none, ← decodeBlocks sc name blocks⟩, [], [], false⟩

/-- The attributes of a func's results: those after each result that a
comma follows, then those after the last, which the grammar reads as the
item's attributes. A func with no results has no attributes. -/
def funcResultAttrs (results : List (Attr × TextPos)) (resultAttrs : List (List (Attr × TextPos)))
    (attrs : List (Attr × TextPos)) : Except ParseError (List (List Attr)) :=
  match results, attrs with
  | [], (_, p) :: _ => errorAt p "a func with no results has no attributes"
  | _, _ => pure (trimAttrs ((resultAttrs ++ [attrs]).map (·.map (·.1))))

/-- The blocks of a func's body, at `kindPos`. An empty body is no
blocks. -/
def funcBlocks (kindPos : TextPos) : SBody → Except ParseError (List SBlock)
  | .items (_ :: _) _ => errorAt kindPos "a func's body holds blocks, not a dialect set"
  | .items [] (i :: _) => errorAt i.kindPos "a func's body holds blocks, not items"
  | .items [] [] => pure []
  | .blocks bs => pure bs

/-- Decodes an item of kind `func`, at `kindPos`: its parameters and
results keep their attributes, its parameters may end in `...`, and its
body is blocks. -/
def decodeFuncItem (kindPos : TextPos) (name : String) (params : List SDef)
    (paramAttrs : List (List (Attr × TextPos))) (variadic : Option TextPos)
    (results : List (Attr × TextPos)) (resultAttrs : List (List (Attr × TextPos)))
    (attrs : List (Attr × TextPos)) (body : SBody) : Except ParseError (Item d) := do
  let ras ← funcResultAttrs results resultAttrs attrs
  let bs ← funcBlocks kindPos body
  let f ← decodeFunc name params results bs
  pure (.func ⟨f.name, f.params, f.results, f.body,
    trimAttrs (paramAttrs.map fun as => as.map (·.1)), ras, variadic.isSome⟩)

/-- The attributes of an external declaration's results, as a func's:
those after each result that a comma follows, then those after the last.
One with no results has no attributes. -/
def externResultAttrs (results : List (Attr × TextPos))
    (resultAttrs : List (List (Attr × TextPos))) (attrs : List (Attr × TextPos)) :
    Except ParseError (List (List Attr)) :=
  match results, attrs with
  | [], (_, p) :: _ => errorAt p "an extern with no results has no attributes"
  | _, _ => pure (trimAttrs ((resultAttrs ++ [attrs]).map (·.map (·.1))))

/-- An external declaration's result attributes decode exactly when a
func's do, to the same lists. -/
theorem externResultAttrs_eq_ok {results : List (Attr × TextPos)}
    {resultAttrs : List (List (Attr × TextPos))} {attrs : List (Attr × TextPos)}
    {x : List (List Attr)} :
    externResultAttrs results resultAttrs attrs = .ok x ↔
      funcResultAttrs results resultAttrs attrs = .ok x := by
  match results, attrs with
  | [], _ :: _ => simp [externResultAttrs, funcResultAttrs, errorAt]
  | [], [] => exact Iff.rfl
  | _ :: _, _ => exact Iff.rfl

/-- Decodes an external declaration, an item of kind `extern`, at `kindPos`
(ADR-2026-11-09-1547): its header as a func's, whose parameters and
results keep their attributes and whose parameters may end in `...`, and
an empty body. Its signature decodes as a function's with no blocks: its
result types, then its parameters, each named once. -/
def decodeExternItem (kindPos : TextPos) (name : String) (params : List SDef)
    (paramAttrs : List (List (Attr × TextPos))) (variadic : Option TextPos)
    (results : List (Attr × TextPos)) (resultAttrs : List (List (Attr × TextPos)))
    (attrs : List (Attr × TextPos)) : SBody → Except ParseError (Item d)
  | .blocks [] => do
    let ras ← externResultAttrs results resultAttrs attrs
    let f ← decodeFunc (d := d) name params results []
    pure (.extern ⟨f.name, f.params, f.results,
      trimAttrs (paramAttrs.map fun as => as.map (·.1)), ras, variadic.isSome⟩)
  | _ => errorAt kindPos "an extern has an empty body"

/-- Checks the header of an item other than a `func` or an `extern`: no parameter carries
attributes, the parameters do not end in `...`, and no result that a comma
follows carries attributes. -/
def plainHeader (paramAttrs : List (List (Attr × TextPos))) (variadic : Option TextPos)
    (resultAttrs : List (List (Attr × TextPos))) : Except ParseError Unit :=
  match paramAttrs.flatten, variadic, resultAttrs.flatten with
  | (_, p) :: _, _, _ => errorAt p "only a func's or an extern's parameters carry attributes"
  | [], some p, _ => errorAt p "only a func's or an extern's parameters end in ..."
  | [], none, (_, p) :: _ => errorAt p "only a func's or an extern's results carry attributes"
  | [], none, [] => pure ()

/-- Checks the header of an item of kind `module`: it has no parameters,
results or attributes. -/
def moduleHeader : List SDef → List (Attr × TextPos) → List (Attr × TextPos) →
    Except ParseError Unit
  | x :: _, _, _ => errorAt x.pos "a module has no parameters"
  | [], (_, p) :: _, _ => errorAt p "a module has no results"
  | [], [], (_, p) :: _ => errorAt p "a module has no attributes"
  | [], [], [] => pure ()

/-- Decodes an item of a dialect's kind `kind`, at `kindPos`: its body is
empty, its result types and its parameters' types decode, and its
attributes stay generic terms. -/
def decodeDialectItem (kind : String) (kindPos : TextPos) (name : String) (params : List SDef)
    (results attrs : List (Attr × TextPos)) : SBody → Except ParseError (Item d)
  | .blocks [] => do
    let results ← results.mapM fun (a, p) => decodeType a p
    let params ← params.mapM decodeDef
    pure (.dialect ⟨kind, name, params, results, attrs.map (·.1)⟩)
  | _ => errorAt kindPos "an item of a dialect's kind has an empty body"

/-- Decodes a field of an aggregate's layout, at its position. -/
def decodeField : Attr × TextPos → Except ParseError (Field d)
  | (a, p) => match Field.decode a with
    | some f => pure f
    | none => errorAt p ("not a field of an aggregate's layout, which is written " ++
        "field(offset, type) or field(offset, type, count), each number at most 2^64 - 1")

/-- Decodes an aggregate's layout (ADR-2026-11-16-1546): it has no
parameters or results and an empty body, and its attributes are its memory,
size and alignment, then its fields. -/
def decodeAggregate (kindPos : TextPos) (name : String) : List SDef → List (Attr × TextPos) →
    List (Attr × TextPos) → SBody → Except ParseError (Item d)
  | x :: _, _, _, _ => errorAt x.pos "an aggregate has no parameters"
  | [], (_, p) :: _, _, _ => errorAt p "an aggregate has no results"
  | [], [], (m, pm) :: (s, ps) :: (a, pa) :: fs, .blocks [] =>
    match Aggregate.decodeNumber "memory" m, Aggregate.decodeNumber "size" s,
        Aggregate.decodeNumber "align" a with
    | some mem, some size, some align => do
      pure (.aggregate ⟨name, mem, size, align, ← fs.mapM decodeField⟩)
    | none, _, _ => errorAt pm "an aggregate's layout writes memory(N) first, N at most 2^64 - 1"
    | _, none, _ => errorAt ps "an aggregate's layout writes size(S) second, S at most 2^64 - 1"
    | _, _, none => errorAt pa "an aggregate's layout writes align(A) third, A at most 2^64 - 1"
  | [], [], _ :: _ :: _ :: _, _ => errorAt kindPos "an aggregate has an empty body"
  | [], [], _, _ => errorAt kindPos
    "an aggregate's layout writes memory(N), size(S) and align(A), then its fields"

/-- Decodes a global (ADR-2026-11-09-1546): it has no parameters or
results and an empty body, and its attributes decode. -/
def decodeGlobal (kindPos : TextPos) (name : String) : List SDef → List (Attr × TextPos) →
    List (Attr × TextPos) → SBody → Except ParseError (Item d)
  | x :: _, _, _, _ => errorAt x.pos "a global has no parameters"
  | [], (_, p) :: _, _, _ => errorAt p "a global has no results"
  | [], [], attrs, .blocks [] =>
    match Global.decodeAttrs name (attrs.map (·.1)) with
    | .ok g => pure (.global g)
    | .error (i, m) => errorAt ((i.bind fun i => (attrs[i]?).map (·.2)).getD kindPos) m
  | [], [], _, _ => errorAt kindPos "a global has an empty body"

mutual
/-- Decodes an item: a `func`, a `module`, whose body is its dialect set
and its items (ADR-2026-11-10-1510), or an item of a dialect's kind
(ADR-2026-11-09-1543). An empty body is no blocks, so it is a module with no
items. -/
def decodeItem : SItem → Except ParseError (Item d)
  | ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩ =>
    if kind = "func" then
      decodeFuncItem kindPos name params paramAttrs variadic results resultAttrs attrs body
    else if kind = "extern" then
      decodeExternItem kindPos name params paramAttrs variadic results resultAttrs attrs body
    else plainHeader paramAttrs variadic resultAttrs >>= fun () =>
    if kind = "module" then do
      moduleHeader params results attrs
      match body with
      | .blocks [] => pure (.module name [] [])
      | .blocks (_ :: _) => errorAt kindPos "a module's body holds items, not blocks"
      | .items ds is => do pure (.module name ds (← decodeItems is))
    else if kind = "aggregate" then decodeAggregate kindPos name params results attrs body
    else if kind = "global" then decodeGlobal kindPos name params results attrs body
    else if isDialectWord kind then decodeDialectItem kind kindPos name params results attrs body
    else errorAt kindPos ("unknown item kind " ++ kind ++
      ": the kinds are func, module, aggregate, global, extern and the words of dialects")

/-- Decodes items, in order. -/
def decodeItems : List SItem → Except ParseError (List (Item d))
  | [] => pure []
  | i :: is => do
    let i ← decodeItem i
    pure (i :: (← decodeItems is))
end

/-- Decoding items decodes each, in order. -/
theorem decodeItems_eq_mapM : ∀ is : List SItem,
    decodeItems (d := d) is = is.mapM decodeItem
  | [] => rfl
  | i :: is => by
    rw [decodeItems, List.mapM_cons, decodeItems_eq_mapM is]

/-- Decodes an entry of the data layout, at its position. -/
def decodeMemLayout : Attr × TextPos → Except ParseError MemLayout
  | (a, p) => match MemLayout.decode a with
    | some e => pure e
    | none => errorAt p ("not an entry of the data layout, which is written " ++
        "memory(N, unit(U), pointer(P), little or big), then align(A) and nonintegral if given")

/-- Decodes a module. -/
def decodeModule (m : SModule) : Except ParseError (Module d) := do
  pure ⟨m.dialects, ← m.layout.mapM decodeMemLayout, ← m.items.mapM decodeItem, m.locs⟩

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
