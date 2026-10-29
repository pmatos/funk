import Fir.Text.Grammar

/-!
# The canonical printer

The printer fixes the one spelling of every module: `print(parse(t)) == t`
holds for every printed `t`. Its layout is:

* single spaces between tokens, a space after each comma and colon, and none
  inside parentheses;
* a function's blocks at the indentation of the function, and its ops two
  spaces deeper. A region of an op opens with ` {` at the end of the op's
  line; its blocks are two spaces deeper than the op, and its closing `}` is
  at the op's indentation, followed by the next region or the location
  reference;
* each op on its own line, ending with a space and its location reference;
* one empty line after each function, then the location table, its entries
  indented by two spaces, in the order they are stored;
* a line feed at the end of every line, the last included, and no trailing
  spaces.
-/

namespace Fir

open Text

/-- An attribute, or a type, in text. -/
def Attr.print : Attr → String
  | .word w => w
  | .int i => printInt i
  | .str s => quote s
  | .sym s => "@" ++ s
  | .app h args => h ++ "(" ++ ", ".intercalate (printList args) ++ ")"
where
  printList : List Attr → List String
    | [] => []
    | a :: as => a.print :: printList as

/-- A location reference, `@N`. -/
def printLocRef (r : LocRef) : String := "@" ++ toString r

/-- A location, as it appears in the location table. -/
def Location.print : Location → String
  | .unknown => "unknown"
  | .range f l₁ c₁ l₂ c₂ => s!"{quote f}:{l₁}:{c₁}-{l₂}:{c₂}"
  | .name n => s!"name({quote n})"
  | .callsite callee caller => s!"callsite({printLocRef callee} at {printLocRef caller})"
  | .fused locs => "fused(" ++ ", ".intercalate (locs.map printLocRef) ++ ")"
  | .derived src => s!"derived({printLocRef src})"

variable {d : Dialect} [DialectText d]

/-- Spaces to indent a line by `n`. -/
def indent (n : Nat) : String := "".pushn ' ' n

/-- A definition of a value, `%x: T`. -/
def printDef (x : Name × d.Ty) : String := "%" ++ x.1 ++ ": " ++ (tyAttr x.2).print

/-- A list of definitions, separated by commas. -/
def printDefs (xs : List (Name × d.Ty)) : String := ", ".intercalate (xs.map printDef)

/-- A successor, `^label` or `^label(%a, %b)`. -/
def Succ.print (s : Succ) : String :=
  "^" ++ s.label ++
    if s.args.isEmpty then "" else "(" ++ ", ".intercalate (s.args.map ("%" ++ ·)) ++ ")"

mutual
/-- An op at indentation `n`, with its line feed. -/
def Operation.print (n : Nat) : Operation d → String
  | ⟨results, op, operands, succs, regions, loc⟩ =>
    let lhs := if results.isEmpty then "" else printDefs results ++ " = "
    let head := " ".intercalate (opName op :: (opAttrs op).map Attr.print)
    let uses := operands.map ("%" ++ ·) ++ succs.map Succ.print
    let rhs := if uses.isEmpty then head else head ++ " " ++ ", ".intercalate uses
    indent n ++ lhs ++ rhs ++ Region.printList n regions ++ " " ++ printLocRef loc ++ "\n"

/-- The regions of an op at indentation `n`. -/
def Region.printList (n : Nat) : List (Region d) → String
  | [] => ""
  | ⟨blocks⟩ :: rs => " {\n" ++ Block.printList (n + 2) blocks ++ indent n ++ "}" ++
      Region.printList n rs

/-- Blocks at indentation `n`, their ops two spaces deeper. -/
def Block.printList (n : Nat) : List (Block d) → String
  | [] => ""
  | ⟨label, params, body⟩ :: bs =>
    indent n ++ "^" ++ label ++ (if params.isEmpty then "" else "(" ++ printDefs params ++ ")") ++
      ":\n" ++ Operation.printList (n + 2) body ++ Block.printList n bs

/-- Ops at indentation `n`. -/
def Operation.printList (n : Nat) : List (Operation d) → String
  | [] => ""
  | o :: os => Operation.print n o ++ Operation.printList n os
end

/-- A function, with its line feed. -/
def Func.print (f : Func d) : String :=
  let results :=
    if f.results.isEmpty then "" else " -> " ++ ", ".intercalate (f.results.map (tyAttr · |>.print))
  "func @" ++ f.name ++ "(" ++ printDefs f.params ++ ")" ++ results ++ " {\n" ++
    Block.printList 0 f.body.blocks ++ "}\n"

/-- The location table, which ends the module. -/
def LocTable.print (t : LocTable) : String :=
  "locs {\n" ++ String.join (t.map fun (r, l) => "  " ++ printLocRef r ++ " = " ++ l.print ++ "\n") ++
    "}\n"

/-- A module: its functions, each followed by an empty line, then its table. -/
def Module.print (m : Module d) : String :=
  String.join (m.funcs.map (·.print ++ "\n")) ++ m.locs.print

end Fir
