import Fir.Syntax.Module

/-!
Validation decides which terms are fir programs. As in the WebAssembly
specification, it is a judgement over the abstract syntax, separate from it:
the terms of the previous chapter can say things that make no sense, such
as using a value that is never defined, and validation rules them out.
Execution gives a meaning to valid modules only: the interpreter runs any
module, but only the runs of a valid one mean something
(ADR-2026-10-30-1856).

This chapter gives the rules that hold for every dialect: types, scoping,
SSA dominance, block arguments, successors, terminators, symbols, isolation
from above and locations. Each dialect adds rules for its own ops and types,
a rule over a whole function, and rules for the kinds of region and of item
that it registers, as the last definition of this section says; the core dialect's rules have a section of their own. A text that does not decode is rejected before
validation, by the parser (see the text format chapter).

The rules are propositions. The validation check, at the end of this
chapter, decides them, and `fir-ref validate` runs it.

# Names and their types

A function defines values in three ways: its parameters, the arguments of
its blocks, and the results of its ops. Every definition names the value and
gives its type, so the type of a value can be looked up by its name. The
blocks of a function include, at any depth, the blocks of its ops' regions;
no core op has one, and a region of an op is of a dialect's kind, whose rule
says how values are scoped in it.
-/

namespace Fir

variable {d : Dialect}

/-- The blocks of a function's body. Its entry block is the first. -/
def Func.blocks (f : Func d) : List (Block d) := f.body.blocks

mutual
/-- The blocks of a list of regions, at any depth. -/
def Region.allBlocks : List (Region d) → List (Block d)
  | [] => []
  | ⟨_, bs⟩ :: rs => Block.allBlocks bs ++ Region.allBlocks rs

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

/-- Every op of a function, at any depth: the ops of each of its blocks at
any depth, in order. -/
def Func.allOps (f : Func d) : List (Operation d) := f.allBlocks.flatMap (·.body)

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

/-- Whether the op owns a region of the core's kind. No valid op does: the
kinds of an op's regions are words of dialects. -/
def Operation.ownsCoreRegion (o : Operation d) : Bool := o.regions.any (·.kind.isNone)

/-!
# Symbols

A module is a symbol table: each item's name is a symbol, and ops refer
to functions only through symbols (ADR-2026-10-29-2012). The type of a
function is its parameter types and its result types.

A module nested in another is a symbol table of its own, with its own
dialect set (ADR-2026-11-10-1510). So a module holds a symbol table at each
level of nesting: its own, and that of each nested module, at any depth. An
op refers by symbol only to a function of the table that holds its
function, never into a nested module or out of one, and validation checks
each table with the same rule.
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

/-- A symbol table: the dialect set and the items of a module, or of a
module nested in one. -/
structure SymbolTable (d : Dialect) where
  dialects : List Name
  items : List (Item d)

/-- The functions of a symbol table, in order. The functions of a nested
module are those of its own table. -/
def SymbolTable.funcs (t : SymbolTable d) : List (Func d) :=
  t.items.filterMap Item.func?

/-- The items of a symbol table of the kinds that dialects register, in
order. -/
def SymbolTable.dialectItems (t : SymbolTable d) : List (DialectItem d) :=
  t.items.filterMap Item.dialect?

/-- The type of the function that each symbol of a table names: its first
function with that symbol. -/
def SymbolTable.symbols (t : SymbolTable d) (s : Name) : Option (FuncType d) :=
  (t.funcs.find? (·.name == s)).map Func.type

mutual
/-- The symbol tables that an item holds, at any depth: none for a function
or an item of a dialect's kind, and a nested module's own, then those its
items hold. -/
def Item.tables : Item d → List (SymbolTable d)
  | .func _ | .dialect _ => []
  | .module _ ds is => ⟨ds, is⟩ :: Item.tablesIn is

/-- The symbol tables that a list of items holds, at any depth, in order. -/
def Item.tablesIn : List (Item d) → List (SymbolTable d)
  | [] => []
  | i :: is => i.tables ++ Item.tablesIn is
end

/-- A module's own symbol table: its dialect set and its items. -/
def Module.table (m : Module d) : SymbolTable d := ⟨m.dialects, m.items⟩

/-- Every symbol table of a module: its own, then that of each nested
module, at any depth, each before the tables nested in it. -/
def Module.tables (m : Module d) : List (SymbolTable d) := m.table :: Item.tablesIn m.items

/-- The functions of a list of items are named by some of its symbols, in
order. -/
theorem funcNames_sublist : ∀ is : List (Item d),
    ((is.filterMap Item.func?).map (·.name)).Sublist (is.map Item.name)
  | [] => .slnil
  | .func _ :: is => .cons_cons _ (funcNames_sublist is)
  | .module .. :: is => .cons _ (funcNames_sublist is)
  | .dialect _ :: is => .cons _ (funcNames_sublist is)

/-- Items that are all functions hold no symbol table. -/
theorem Item.tablesIn_eq_nil : ∀ {is : List (Item d)}, (∀ i ∈ is, i.func?.isSome) →
    Item.tablesIn is = []
  | [], _ => rfl
  | .func _ :: _, h => by
    rw [Item.tablesIn, Item.tables, Item.tablesIn_eq_nil fun j hj => h j (List.mem_cons_of_mem _ hj)]
    rfl
  | .module .. :: _, h => absurd (h _ (List.mem_cons_self ..)) (by simp [Item.func?])
  | .dialect _ :: _, h => absurd (h _ (List.mem_cons_self ..)) (by simp [Item.func?])

/-- The tables that an item of a list holds are tables of the list. -/
theorem Item.mem_tablesIn {i : Item d} : ∀ {is : List (Item d)}, i ∈ is →
    ∀ u ∈ i.tables, u ∈ Item.tablesIn is
  | _ :: _, hi, u, hu => by
    rw [Item.tablesIn, List.mem_append]
    rcases List.mem_cons.mp hi with rfl | h
    · exact .inl hu
    · exact .inr (Item.mem_tablesIn h u hu)

/-- A module's own table holds its functions, and gives its symbols. -/
@[simp] theorem Module.table_funcs (m : Module d) : m.table.funcs = m.funcs := rfl

@[simp] theorem Module.table_symbols (m : Module d) : m.table.symbols = m.symbols := rfl

/--
What a dialect's op rules may look at: the module's symbol table and the
result types of the enclosing function.
-/
structure OpContext (d : Dialect) where
  symbols : Name → Option (FuncType d)
  results : List d.Ty

/--
What a dialect's function rule may look at beside the function: the module's
symbol table.
-/
structure FuncContext (d : Dialect) where
  symbols : Name → Option (FuncType d)

/--
How the dialect `d` sees a function of a dialect `host` that holds it. An op
or a type of `host` is one of `d`'s, or is `none`: it belongs to another
dialect of the host. A function rule must still count such an op, because
the op's operands and results are visible whatever its dialect.
-/
structure DialectView (d host : Dialect) where
  op : host.Op → Option d.Op
  ty : host.Ty → Option d.Ty

/-- A dialect's view of its own functions: every op and type is its own. -/
def DialectView.id (d : Dialect) : DialectView d d := ⟨some, some⟩

/--
The rules a dialect adds to validation.

* `validTy` says which of the dialect's types are valid.
* `symbolRefs` lists the symbols an op refers to. Validation checks that each
  one names a function of the module.
* `validOp` is the dialect's own rule for an op, in its context, beyond the
  general rules below. For example, the core dialect requires that `ret`
  returns the function's result types and that `call` matches its callee's
  type.
* `validFunc` is the dialect's own rule for a whole function, for what no op
  can see alone, such as a value that must be used exactly once. The rule
  sees the function of the `host` dialect that holds it, through a view, so
  it also sees the uses by other dialects' ops. Validation calls it on every
  function, also on one that breaks other rules, so it must hold no
  assumption about the function.
* `regionKindNames` lists the region kinds that the dialect registers, each a
  word of the dialect, and `validRegion` is the rule of each: how values are
  scoped in a region of that kind, which of its ops end its blocks, and
  where its successors go. The rule sees the region and the function of the
  `host` dialect that holds it, through a view, as `validFunc` does. A
  dialect that registers no kind, as the core does, has neither.
* `itemKindNames` lists the kinds of item that the dialect registers, each a
  word of the dialect, and `validItem` is the dialect's rule for an item of
  one of them (ADR-2026-11-10-2224). The rule sees the item of the `host`
  dialect that holds it through a view, as `validFunc` does, and the symbols
  of the item's table. It reads the kind from the item, and says what each
  kind's parameters, results and attributes must be. A dialect that
  registers no kind, as the core does, has neither: the core's kinds,
  `func` and `module`, are terms of their own.
-/
class DialectValidation (d : Dialect) where
  validTy : d.Ty → Prop
  symbolRefs : d.Op → List Name
  validOp : OpContext d → d.Op → Prop
  validFunc : {host : Dialect} → DialectView d host → FuncContext host → Func host → Prop
  regionKindNames : List Name := []
  validRegion : {host : Dialect} → DialectView d host → Name → FuncContext host → Func host →
    Region host → Prop := fun _ _ _ _ _ => False
  itemKindNames : List Name := []
  validItem : {host : Dialect} → DialectView d host → FuncContext host → DialectItem host →
    Prop := fun _ _ _ => False
export DialectValidation (validTy symbolRefs validOp validFunc regionKindNames validRegion
  itemKindNames validItem)

end Fir
