import Fir.Text.Print
import Fir.Validation.Scope

/-!
# Round trips

Two properties tie the parser to the printer (P3, ADR-2026-10-29-2014):

* `parse(print(m)) == m` for every module `m` that can be written;
* `print(parse(t)) == t` for every printed text `t`.

The second follows from the first. They hold for the modules whose printed
form says everything the module holds: every name, word and attribute can be
written as a token, and every op can be read back from its name, its
attributes and the types of its operands and results. These conditions are
syntactic. Validation implies most of them, but a module need not be valid to
round-trip. #10 writes the parser, and #11 proves the first property.

The conditions look at every block and op of a function, at any depth: the
blocks of the regions of its ops too.
-/

namespace Fir

open Text

variable {d : Dialect}

mutual
/-- The blocks of a list of regions, at any depth. -/
def Region.allBlocks : List (Region d) → List (Block d)
  | [] => []
  | ⟨bs⟩ :: rs => Block.allBlocks bs ++ Region.allBlocks rs

/-- These blocks and the blocks of their ops' regions, at any depth. -/
def Block.allBlocks : List (Block d) → List (Block d)
  | [] => []
  | ⟨l, ps, body⟩ :: bs => ⟨l, ps, body⟩ :: Operation.regionBlocks body ++ Block.allBlocks bs

/-- The blocks of the regions of these ops, at any depth. -/
def Operation.regionBlocks : List (Operation d) → List (Block d)
  | [] => []
  | ⟨_, _, _, _, regions, _⟩ :: os => Region.allBlocks regions ++ Operation.regionBlocks os
end

/-- Every block of a function, at any depth. -/
def Func.allBlocks (f : Func d) : List (Block d) := Block.allBlocks f.body.blocks

/-- Every op of a function, at any depth. -/
def Func.allOps (f : Func d) : List (Operation d) := f.allBlocks.flatMap (·.body)

/-- Every value a function defines, at any depth, with its type. -/
def Func.allDefs (f : Func d) : List (Name × d.Ty) :=
  f.params ++ f.allBlocks.flatMap Block.defs

/-- The type of a value, looked up among every definition of the function. -/
def Func.typeOfAny (f : Func d) (x : Name) : Option d.Ty :=
  (f.allDefs.find? (·.1 == x)).map (·.2)

mutual
/-- An attribute can be written as a token. -/
def Attr.Writable : Attr → Prop
  | .word w | .sym w => isWord w
  | .int _ | .str _ => True
  | .app h args => isWord h ∧ args ≠ [] ∧ Attr.AllWritable args

/-- Every attribute of a list can be written. -/
def Attr.AllWritable : List Attr → Prop
  | [] => True
  | a :: as => a.Writable ∧ Attr.AllWritable as
end

/-- A type is written as a word, or a word applied to attributes. -/
def Attr.IsType : Attr → Prop
  | .word w => isWord w
  | .app h args => isWord h ∧ args ≠ [] ∧ Attr.AllWritable args
  | _ => False

variable [DialectSignature d] [DialectText d]

/-- An op can be written, and read back from its context. -/
def Func.OpWellFormed (f : Func d) (o : Operation d) : Prop :=
  isWord (opName o.op) ∧ Attr.AllWritable (opAttrs o.op) ∧
  o.operands.map f.typeOfAny = (sig o.op).map some ∧
  o.results.map (·.2) = returnTypes o.op ∧
  ∀ s ∈ o.succs, isName s.label ∧ ∀ a ∈ s.args, isName a

/--
A function can be written and read back: its symbol is a word; its value
names are unique and can be written; its labels can be written; its types are
written as types; and each of its ops can be written and read back.
-/
structure Func.WellFormed (f : Func d) : Prop where
  name : isWord f.name
  namesUnique : (f.allDefs.map (·.1)).Nodup
  names : ∀ x ∈ f.allDefs, isName x.1
  labels : ∀ b ∈ f.allBlocks, isName b.label
  types : ∀ t ∈ f.results ++ f.allDefs.map (·.2), (tyAttr t).IsType
  ops : ∀ o ∈ f.allOps, f.OpWellFormed o

/-- A module can be written and read back. Any location table can. -/
def Module.WellFormed (m : Module d) : Prop := ∀ f ∈ m.funcs, f.WellFormed

/-- A parser: from text to a module, or to an error. -/
abbrev Parser (d : Dialect) := String → Except String (Module d)

/-- `parse(print(m)) == m` for every module that can be written. -/
def PrintThenParse (parse : Parser d) : Prop :=
  ∀ m : Module d, m.WellFormed → parse m.print = .ok m

/-- `print(parse(t)) == t` for every printed text `t`. -/
def ParseThenPrint (parse : Parser d) : Prop :=
  ∀ m₀ : Module d, m₀.WellFormed → ∀ m, parse m₀.print = .ok m → m.print = m₀.print

/-- The second round trip follows from the first. -/
theorem parseThenPrint_of_printThenParse {parse : Parser d}
    (h : PrintThenParse parse) : ParseThenPrint parse := by
  intro m₀ hw m hp
  rw [h m₀ hw] at hp
  cases hp
  rfl

end Fir
