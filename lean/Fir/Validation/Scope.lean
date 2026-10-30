import Fir.Syntax.Module

/-!
Validation decides which terms are fir programs. Like the Wasm spec, it is a
judgement over the abstract syntax, separate from it: the terms of the
previous chapter can say things that make no sense, such as using a value
that is never defined, and validation rules them out. Execution is defined
for valid modules only.

This chapter gives the rules that hold for every dialect: types, scoping,
SSA dominance, block arguments, successors, terminators, symbols, isolation
from above and locations. Each dialect adds rules for its own ops and types
through the class `DialectValidation`, defined below; the core dialect's
rules have a section of their own. A text that does not decode is
rejected before validation, by the parser (see the text format chapter).

The rules are propositions. The executable check that `fir-ref validate`
runs (#10) is written against them.

# Names and their types

A function defines values in three ways: its parameters, the arguments of
its blocks, and the results of its ops. Every definition names the value and
gives its type, so the type of a value can be looked up by its name. The
blocks of a function include, at any depth, the blocks of its ops' regions;
no core op has one.
-/

namespace Fir

variable {d : Dialect}

/-- The blocks of a function's body. Its entry block is the first. -/
def Func.blocks (f : Func d) : List (Block d) := f.body.blocks

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
def Func.allBlocks (f : Func d) : List (Block d) := Block.allBlocks f.blocks

/-- The values a block defines: its arguments, then its ops' results. -/
def Block.defs (b : Block d) : List (Name × d.Ty) :=
  b.params ++ b.body.flatMap (·.results)

/-- Every value a function defines, at any depth, with its type. -/
def Func.defs (f : Func d) : List (Name × d.Ty) :=
  f.params ++ f.allBlocks.flatMap Block.defs

/-- The type of the value named `x` in a function, if the function defines it. -/
def Func.typeOf (f : Func d) (x : Name) : Option d.Ty :=
  (f.defs.find? (·.1 == x)).map (·.2)

/-- Every type that a function's text states: its signature and every definition. -/
def Func.types (f : Func d) : List d.Ty :=
  f.results ++ f.defs.map (·.2)

/-- The block with label `l`, if the function has one. -/
def Func.block? (f : Func d) (l : Name) : Option (Block d) :=
  f.blocks.find? (·.label == l)

/-- The values an op uses: its operands, then the arguments it passes to its
successors. -/
def Operation.uses (o : Operation d) : List Name :=
  o.operands ++ o.succs.flatMap (·.args)

/-!
# Symbols

A module is a symbol table: each function's name is a symbol, and ops refer
to functions only through symbols (H3). The type of a function is its
parameter types and its result types.
-/

/-- The type of a function: what it takes and what it returns. -/
structure FuncType (d : Dialect) where
  params : List d.Ty
  results : List d.Ty

/-- The type of a function. -/
def Func.type (f : Func d) : FuncType d := ⟨f.params.map (·.2), f.results⟩

/-- The module's symbol table: the type of the function each symbol names. -/
def Module.symbols (m : Module d) (s : Name) : Option (FuncType d) :=
  (m.funcs.find? (·.name == s)).map Func.type

/--
What a dialect's op rules may look at: the module's symbol table and the
result types of the enclosing function.
-/
structure OpContext (d : Dialect) where
  symbols : Name → Option (FuncType d)
  results : List d.Ty

/--
The rules a dialect adds to validation.

* `validTy` says which of the dialect's types are valid.
* `symbolRefs` lists the symbols an op refers to. Validation checks that each
  one names a function of the module.
* `validOp` is the dialect's own rule for an op, in its context, beyond the
  general rules below. For example, the core dialect requires that `ret`
  returns the function's result types and that `call` matches its callee's
  type.
-/
class DialectValidation (d : Dialect) where
  validTy : d.Ty → Prop
  symbolRefs : d.Op → List Name
  validOp : OpContext d → d.Op → Prop
export DialectValidation (validTy symbolRefs validOp)

end Fir
